#include <mpi.h>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <cstdlib>
#include <sys/wait.h>
#include <stdlib.h>
#include <algorithm>
#include <assert.h>
#include <bits/stdc++.h>
#include <set>
#include <map>
#include <chrono>
#include <queue>
#include <fcntl.h> 
#include <unistd.h>
using namespace std;


// --- SET THE SAT SOLVER AND PROOF TRIMMER ---

// Path for the SAT solver.
static string  solver  = "/usr/local/bin/kissat";    // should include full path
static string  solverWithoutPath = "kissat";         // basename of th previous line

// Path for the proof trimmer.
static string  trimmer = "/usr/local/bin/dpr-trim";  // should include full path

// --- DO NOT CHANGE ANYTHING BELOW THIS LINE ---


constexpr int SAT   = 10;
constexpr int UNSAT = 20;
constexpr int INTERRUPTCONFIRMATION = 100;

string gcnfFile="nullFile";
string proofFile="nullFile";
string explanationFile="nullFile";
string outFile="nullFile";

// --------------------------------------------------
// MPI message tags
// --------------------------------------------------
static const int TAG_JOB    = 1;
static const int TAG_RESULT = 2;
static const int TAG_STOP   = 3;
static const int TAG_INTERRUPT = 4;
static const int TAG_TERMINATE = 5;

struct ExtendedClause{
  int constraintNum;
  vector<int> clause;
};

vector<ExtendedClause> extendedClauses;
vector<vector<int> > clausesOfConstraint;
map<int,string> constraintReasons;
vector<vector<int> > clausesFixpoint;
set<int>       setOfConstraintsPending;
vector<int> vectorOfConstraintsPending;
vector<int> vectorOfConstraintsPendingNextRound;
vector<int> vectorOfConstraintsNeeded;
map< vector<int>, set<int> > constraintNumsOfClause;
vector<char> inputBuffer;
long inputBufferSize = 0;
int numVars = 0, numClauses = 0, numConstraints = 0, numConstraintsPending = 0;

auto start = chrono::steady_clock::now();

int fpStrategy = 2;     // default: while at least 20% improvement;
int fpPercent  = 20;  //
int fpTimes = 5;        //
int numClausesAfterFixpoint;

string timeString() {
    auto now = chrono::system_clock::now();
    auto us = chrono::duration_cast<chrono::microseconds>(now.time_since_epoch()) % 1000000;
    time_t now_c = chrono::system_clock::to_time_t(now);
    tm now_tm = *localtime(&now_c);      // Convert to local time structure
    ostringstream oss;
    oss << put_time(&now_tm, "%Y%m%d_%H%M%S") << "_" << setfill('0') << setw(6) << us.count();
    return oss.str();
}

static string timestampString = timeString();

void showWallClockTime() {
  auto end = chrono::steady_clock::now();
  auto duration = chrono::duration_cast<chrono::milliseconds>(end - start);
  float seconds = (float)duration.count()/1000.0;
  cout << "Wall clock time elapsed: " << seconds << " s" << endl;
}


void printQueue(queue<int> q) {
    while (!q.empty()) {
        cout << q.front() << " ";
        q.pop();
    }
    cout << endl;
}

void printSet(set<int> set) {
  for (int c: set) cout << c << " ";    cout << endl;
}


void readExplanationFile( ){
  if ( explanationFile == "nullFile" ) return;
  ifstream file(explanationFile);
  if (!file) { cerr << "Failed to open file\n"; MPI_Abort(MPI_COMM_WORLD, 1);   }
  string line;
  while (getline(file, line)) {
    istringstream iss(line);
    int N;
    string S;
    if (!(iss >> N)) { continue; } // Read integer skipping any malformed lines 
    if (!(iss >> quoted(S))) { continue; } // Read quoted string skipping any malformed lines
    constraintReasons[N] = S;
  }
}


void fixpoint( int fpStrategy, int fpTimes, int fpPercent ) {
  static string  gcnf2cnfCall   = "./gcnf2cnf " + gcnfFile + " > " + timestampString + "tmpClauses.cnf" ;
  int result = system(gcnf2cnfCall.c_str());

  if ( proofFile == "nullFile" ) { 
    cout << "No initial proof file given. Re-running SAT solver to generate it... " << endl;
    string  solverCall = solver + " " + timestampString + "tmpClauses.cnf proof.proof > /dev/null" ;
    int result = system(solverCall.c_str());
    if ( WEXITSTATUS(result)!=20) { cout << "not unsat!     " << endl; exit(1); }
    cout << "   ... OK, Unsat result found and proof generated. " << endl;
    proofFile = "proof.proof";
  }

  
  static string  trimmerCall   = trimmer + " " + timestampString + "tmpClauses.cnf " + proofFile + " -c " + timestampString + "core.cnf  > /dev/null" ;
  //  cout << "before trimmer call: ";  showWallClockTime();  
  result = system(trimmerCall.c_str());
  //cout << "after trimmer call: ";  showWallClockTime();
  
  if ( WEXITSTATUS(result)!=0) { cout << "dpr-trim failed!" << endl; exit(1); }
  static string  mvCall   = "mv " + timestampString + "core.cnf  " + timestampString + "tmpClauses.cnf ";
  result = system(mvCall.c_str());
  string aux;
  int numFPClauses=numClauses;
  int newNumFPClauses;
  string tmpClausesName = timestampString + "tmpClauses.cnf";
  fstream FPClauses1( tmpClausesName.c_str(), fstream::in);
  FPClauses1 >> aux >> aux >> aux >> newNumFPClauses;
  FPClauses1.close();
  //  cout << "after first trim: ";  showWallClockTime();
  
  if (fpStrategy==0) cout << "Reducing core until fixpoint... " << endl;
  if (fpStrategy==1) cout << "Reducing core " << fpTimes << " times unless fixpoint is reached before that. " << endl;
  if (fpStrategy==2) cout << "Reducing core while at least " << fpPercent << "% improvement. " << endl;  
  cout << "Num clauses: " << newNumFPClauses << " (initial core) " << endl;  
  
  if ( newNumFPClauses == numFPClauses ) { cout << "fixpoint! " << endl; return; }

  while ( true ) {  // do 1 fixpoint iteration:
    if ( fpStrategy==1 and fpTimes == 0 ) break;
    numFPClauses = newNumFPClauses;
    string  solverCall = solver + " " + timestampString + "tmpClauses.cnf " + timestampString +"proof.proof > /dev/null" ;
    result = system(solverCall.c_str());
    if ( WEXITSTATUS(result)!=20) { cout << "not unsat!     " << endl; exit(1); }
    static string  trimmerCall = trimmer + " " + timestampString+"tmpClauses.cnf " + timestampString+"proof.proof -c "
                                         + timestampString+"core.cnf  > /dev/null" ; 		
    result = system(trimmerCall.c_str());
    if ( WEXITSTATUS(result)!=0) { cout << "dpr-trim failed!" << endl; exit(1); }
    string mvCall = "mv " + timestampString + "core.cnf " + timestampString + "tmpClauses.cnf ";
    result = system(mvCall.c_str());
    fstream FPClauses(tmpClausesName.c_str(), fstream::in);
    FPClauses >> aux >> aux >> aux >> newNumFPClauses;
    FPClauses.close();
    cout << "Num clauses: "<< newNumFPClauses << endl;
    if ( newNumFPClauses == numFPClauses ) { cout << "fixpoint! " << endl; break; }
    if ( fpStrategy==1 ) {      if ( --fpTimes == 0 ) break; }
    if ( fpStrategy==2 ) {
      int percentageImprovement = trunc( 100 * (numFPClauses - newNumFPClauses) / numFPClauses );
      if ( percentageImprovement < fpPercent ) break;
    }
  }
  fstream FPClauses2(tmpClausesName.c_str(), fstream::in);      // Read result of fixpoint computation from file tmpClauses.cnf into clausesFixpoint:
  FPClauses2 >> aux >> aux >> aux >> numClausesAfterFixpoint;
  clausesFixpoint.resize(numClausesAfterFixpoint);  
  for (int i=0; i<numClausesAfterFixpoint; ++i) {
    int lit;
    while (FPClauses2 >> lit and lit != 0) clausesFixpoint[i].push_back(lit);
  }
  FPClauses2.close();
  for (int i=0; i<numClausesAfterFixpoint; ++i)  sort( clausesFixpoint[i].begin(), clausesFixpoint[i].end() );
}


void readExtendedClausesIntoTextBuffer() {  // only master does this
  FILE* f = fopen(gcnfFile.c_str(), "rb");
  if (!f) { cerr << "ERROR: Cannot open " << gcnfFile << endl; MPI_Abort(MPI_COMM_WORLD, 1);  }
  fseek(f, 0, SEEK_END);
  inputBufferSize = ftell(f);
  fseek(f, 0, SEEK_SET);
  inputBuffer.resize(inputBufferSize);
  auto x = fread(inputBuffer.data(), 1, inputBufferSize, f);
  fclose(f);
}



void parseInputBufferIntoExtendedClauses(int rank) { // master and all workers do this
  string_view text{inputBuffer.data()};
  istringstream input{string(text)};
  string p, format;
  int numConstraints0;
  input >> p >> format >> numVars >> numClauses >> numConstraints0;
  numConstraints = numConstraints0 + 1;
  if (rank == 0) cout << "Read "<< numVars << " vars, " << numClauses << " clauses, and " << numConstraints << " constraints." << endl;
  if (p != "p" || format != "gcnf") { cout << "Invalid header line" << endl; }
  extendedClauses.reserve(numClauses);
  while (input) {
    ExtendedClause ec;
    int literal;
    char openBrace, closeBrace;
    if (!(input >> openBrace >> ec.constraintNum >> closeBrace)) break;  // end of input
    if (openBrace != '{' || closeBrace != '}') cout << "Invalid constraint format" << endl;
    ec.clause.clear();
    while (input >> literal && literal != 0) ec.clause.push_back(literal);
    extendedClauses.push_back(move(ec));
  }
  if ((int)extendedClauses.size() != numClauses) {
    cerr << "Wrong number of clauses! Read: " << extendedClauses.size() << "\n";
    MPI_Abort(MPI_COMM_WORLD, 1);
  }
}


void printHelp()	{
  cout << " " << endl;
  cout << "Usage: WhyUnsat  <options>  <fileName>.gcnf " << endl;
  cout << " where <options> include:" << endl;
  cout << "  -fp                    trim until fixpoint.                                                           " << endl;
  cout << "  -times T               do T trimming iterations, with T>=0.                                           " << endl;
  cout << "  -percent P             trim until improvement less than P percent (default, with P=20%).              " << endl;
  cout << "  -proof proofFile       optional initial proof file to start trimming, instead of the gcnf.            " << endl;
  cout << "  -exp explanationFile   optional file with lines: <constraintNum> \"text describing this constraint\". " << endl;
  cout << "  -output outputFile     optional file into which the final MUS will be written.                        " << endl;
  cout << "  -help                  print this help.                                                               " << endl;  
  cout << " " << endl;
}



void computeHittingSet() {
  for (int i=0; i<numClausesAfterFixpoint; ++i)  {   // For clauses with single ct c, insert c into setOfConstraintsPending (if not already there).
    set<int> cNums = constraintNumsOfClause[ clausesFixpoint[i] ];
    if (cNums.size()==0) {
      cerr<< " ERROR: Trimmer has returned clause in core that is not in original cnf!!! " << endl;
      MPI_Abort(MPI_COMM_WORLD, 1); 
    }
    if ( cNums.size()==1 ) setOfConstraintsPending.insert( *cNums.begin() ); 
  }
  vector<set<int>> setsStillToBeHit;
  for (int i=0; i<numClausesAfterFixpoint; ++i)  {                       //  now, for each clause,
    set<int> cNums = constraintNumsOfClause[ clausesFixpoint[i] ];	   //  if none of clause's constraints is in setOfConstraintsPending
    bool hit=false;							   //  then store clause's constraints in setsStillToBeHit
    for (int c: cNums) if (setOfConstraintsPending.find(c) != setOfConstraintsPending.end() ) { hit=true; break; }
    if (!hit) setsStillToBeHit.push_back(cNums);                             
  }
  while (setsStillToBeHit.size() != 0) { // Greedy:  While setsStillToBeHit non-empty, add most frequent elem e and remove the sets with e
    map<int,int> frequencies;
    for ( set<int> cNums : setsStillToBeHit )  for ( int c:cNums ) frequencies[c]++;
    int maxFreq=-1;
    int maxElem=-1;      
    for (const auto& pairCF : frequencies)
      if ( pairCF.second > maxFreq ) {
	maxFreq = pairCF.second;
	maxElem = pairCF.first;
      }
    setOfConstraintsPending.insert( maxElem );
    vector<set<int>> setsStillToBeHit1 = setsStillToBeHit;
    setsStillToBeHit.clear();
    for ( set<int> cNums : setsStillToBeHit1 )  if (cNums.find(maxElem) == cNums.end() ) setsStillToBeHit.push_back(cNums);
  }
}

void checkResultUnsatAndMinimality() {      // checking result: unsat with solver, and minimality with muser2
  vector<ExtendedClause> ve;
  for ( int i=0; i < vectorOfConstraintsNeeded.size(); i++ ) {
    int c = vectorOfConstraintsNeeded[i];
    for ( int j: clausesOfConstraint[c] ) ve.push_back({i, extendedClauses[j].clause });
  }

  string checkfile = timestampString + "unsatCheck.cnf";

  ofstream outc(checkfile.c_str());
  outc << "p cnf " << numVars << " " << ve.size() << "\n";
    
  for (const auto &c : ve) {
    for ( int lit: c.clause ) outc << lit << " ";
    outc << " 0 " << endl;
  }
  outc.close();
  cout << "Checking unsat of this result:   " << flush;
  string solverCommand = solver + " " + checkfile + " > /dev/null";
  int status = system(solverCommand.c_str());
  if ( WEXITSTATUS(status) == 20 ) {
    cout << "ok" << endl;
    string rmchk = "rm " + checkfile;
    status = system(rmchk.c_str());
  } else {
    cout << "WRONG RESULT!" << endl;
    MPI_Abort(MPI_COMM_WORLD, 1);
  }
    
  string muserCheckFile = timestampString + "muserCheck.gcnf";
  ofstream outm(muserCheckFile.c_str());
  outm << "p gcnf " << numVars << " " << ve.size() << " " << vectorOfConstraintsNeeded.size()-1 << "\n";
  for (const auto &c : ve) {
    outm << "{" << c.constraintNum << "}  ";
    for ( int lit: c.clause ) outm << lit << " ";
    outm << " 0 " << endl;
  }
  outm.close();
  string checkCall = "./muser2 -ipasir -w -grp " + muserCheckFile + " > /dev/null ";
  cout << "Num constraints needed of this WhyUnsat result according to muser2:   " << flush;
  status = system( checkCall.c_str() );
  status = system("egrep -o \"\{(.*)}\" muser2-output.gcnf | sort -u > tmp2 ; cat tmp2 | wc -l ");
}


void runWithMuser2() {
    cout << endl << endl << "Running our input problem with muser2: " << endl;
    string solverCommand = "./muser2 -ipasir -w -grp " + gcnfFile + "| egrep \"c CPU Time\" ";
    int status = system(solverCommand.c_str());
    status = system("egrep -o \"\{(.*)}\" muser2-output.gcnf > tmp1; sed 's/[{}]//g' tmp1 > tmp2;  sort -g -u tmp2 > tmp3; cat tmp3; echo -n \"Num constraints: \"; cat tmp3 | wc -l");
}


void prepareCNFFileForWorker(int job) {
  string  headerFilename = timestampString + "header_"  + to_string(job) ;
  string clausesFilename = timestampString + "clauses_" + to_string(job) ;
  string     cnfFilename = timestampString + "job_"     + to_string(job) + ".cnf";
  int numClausesJob = 0;
  
  ofstream outClauses(clausesFilename);  // write clauses file:
  for (const auto &c : extendedClauses)
    if (c.constraintNum != job  and  setOfConstraintsPending.find(c.constraintNum) != setOfConstraintsPending.end()	) {
      for ( int lit: c.clause ) outClauses << lit << " ";
      outClauses << " 0 " << endl;
      numClausesJob++;
    }
  outClauses.close();
  ofstream outHeader(headerFilename);  // write header file:
  outHeader << "p cnf " << numVars << " " << numClausesJob << "\n";
  outHeader.close();
  string catCommand = "cat " + headerFilename + " " + clausesFilename + " > " + cnfFilename;
  int statusCat = system(catCommand.c_str());
  string rmCommand = "rm " + headerFilename + " " + clausesFilename;
  int statusRm = system(rmCommand.c_str());
}
  
void shutUpSolverOutput() {
  int fd = open("/dev/null", O_WRONLY);
  if (fd != -1) {
    dup2(fd, STDOUT_FILENO);  	    // Redirect STDOUT (1) and STDERR (2) of solver to /dev/null
    dup2(fd, STDERR_FILENO);
    close(fd); 	                    // Close the original file descriptor (no longer needed)
  }
}


void worker(int rank) {  
    MPI_Status status;
    int jobRunning = -1;    // negative means no job running
    pid_t pidJob = -1;      // meaningful only when job running and then pidJob > 0
    int status_val;
    int flag;
    MPI_Request request;
    int resMsg[2];
    int msgIntConf[2];

    while (true) {  // Polling loop: Wait for child or MPI message
      
      MPI_Iprobe( 0, MPI_ANY_TAG, MPI_COMM_WORLD, &flag, &status);   // Non-blocking check for incoming message
      
      if ( !flag and jobRunning >= 0 ) {                // ============== Do Non-blocking check whether child finished
	pid_t result = waitpid(pidJob, &status_val, WNOHANG);
	if (result == pidJob) {               // Child finished
	  int toolResult;
	  if (WIFEXITED(status_val))  toolResult = WEXITSTATUS(status_val); // SAT/UNSAT code
	  string cnfFilename = timestampString + "job_"     + to_string(jobRunning) + ".cnf";
	  string rmCommand = "rm -f " + cnfFilename;
	  int statusRm = system(rmCommand.c_str());
	  //	  cout << "Worker " << rank << " detects job " << jobRunning << " has finished with result " << toolResult << endl;
	  resMsg[0] = jobRunning;
	  resMsg[1] = toolResult;
	  jobRunning = -1;
	  pidJob = -1;
	  MPI_Isend(resMsg, 2, MPI_INT, 0, TAG_RESULT, MPI_COMM_WORLD, &request);
	} else if (result == -1) {
	  cout << endl << endl << "ERROR -1 in worker " << rank << ": job " << jobRunning << endl << endl;
	  // Error: Child might have been reaped elsewhere or never existed
	  if (errno == ECHILD) {
	    // Log this! It means the child is gone but we missed the exit status.
	    cout << endl << endl << "ECHILD! " << rank << ": job " << jobRunning << endl << endl;
	  }
	} // else { 	  // result == 0: Child is still alive. Carry on.	}
      }
      
      if (!flag) {
	this_thread::sleep_for(chrono::milliseconds(10));  // Small sleep to prevent 100% CPU usage during polling
	//	if ( jobRunning >= 0 ) cout << "Worker " << rank << " still busy with job " << jobRunning << endl;
	//	else                   cout << "Worker " << rank << " is waiting doing nothing. " << endl;
	continue;
      } 
	        
      if (status.MPI_TAG == TAG_TERMINATE) {
	MPI_Recv(NULL, 0, MPI_INT, 0, TAG_TERMINATE, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
	//	cout << "Worker " << rank << " terminated. " << endl;
	break;
      }
      
      if (status.MPI_TAG == TAG_INTERRUPT) {
	int newlyUnsat;
	MPI_Recv( &newlyUnsat, 1, MPI_INT, 0, TAG_INTERRUPT, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
	setOfConstraintsPending.erase(newlyUnsat);
	if (jobRunning >= 0) { // need to ask if job running: if it was this worker that notified the unsat, then it has none
	  //	  cout << "Worker " << rank << " received interrupt due to unsat of " << newlyUnsat << ". Stopping job: " << jobRunning << endl;
	  if (pidJob < 0 ) cout << "Worker " << rank << " is killing existing job " << jobRunning << " but pidJob < 0! " << endl;
	  else             kill(pidJob, SIGTERM); 
	  // cout << "Worker " << rank << " sent kill to job " << jobRunning << endl;
	  waitpid(pidJob, &status_val, 0); // Clean up zombie process
	  // cout << "Worker " << rank << " cleaned up zombie process of job " << jobRunning << endl;
	  jobRunning = -1;
	  pidJob = -1;
	}
	msgIntConf[0] = newlyUnsat;
	msgIntConf[1] = INTERRUPTCONFIRMATION;
	MPI_Send(msgIntConf, 2, MPI_INT, 0, TAG_RESULT, MPI_COMM_WORLD);
	// cout << "Worker " << rank << " has sent confirmation of interrupt of job " << job << endl;
	continue;
      }      
	    
      if (status.MPI_TAG == TAG_JOB) {	
	int job;
	MPI_Recv(&job, 1, MPI_INT, 0, TAG_JOB, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
	if (jobRunning >= 0) {
	  // cout << "Worker " << rank << " receives new job " << job << " but already has job " << jobRunning << " running!" << endl;
	  continue;
	}
	if (pidJob >= 0) {
	  // cout << "Worker " << rank << " receives new job " << job << " but pidJob is >= 0! " << endl;
	  continue;
	}
	pidJob = fork(); // Create a child process
	if (pidJob  < 0) { perror("Fork failed"); continue; }
	if (pidJob == 0) {    // --- Child Process ---
	  prepareCNFFileForWorker(job);
	  shutUpSolverOutput();
	  string cnfFilename = timestampString + "job_"     + to_string(job) + ".cnf";
	  execl( solver.c_str(), solverWithoutPath.c_str(),  cnfFilename.c_str(),  nullptr);
	  cout << "execl failed: " << strerror(errno) << " (Path: " << solver << ")" << endl;
	  _exit(1); // if execl succeeds the child process disappears
	} else {           // --- Parent Process ---
	  jobRunning=job;
	}
      }
      
    } // while true
}


void master(int world_size) {
    queue<int> pending;
    for ( int c: setOfConstraintsPending ) pending.push(c);

    //    cout << "Constraints pending initially: "; printQueue(pending);
    
    int active_workers = 0;
    
    // ---- initial dispatch ----
    for (int w = 1; w < world_size && !pending.empty(); ++w) {
      int job = pending.front(); pending.pop();
      MPI_Send(&job, 1, MPI_INT, w, TAG_JOB, MPI_COMM_WORLD);
      active_workers++;
      //cout << "Sent to worker " << w << ": job " << job << endl;
    }
    
    while (!pending.empty() || active_workers > 0) {
      MPI_Status st;
      int msg[3];
      MPI_Recv(msg, 2, MPI_INT, MPI_ANY_SOURCE, TAG_RESULT, MPI_COMM_WORLD, &st);
      int worker = st.MPI_SOURCE;
      int job    = msg[0];
      int res    = msg[1];
      active_workers--;

      if (res == SAT) {
	setOfConstraintsPending.erase(job); 
	cout << "Needed:      " << fixed<<setw(3)<<setfill(' ')<< job << "  " << constraintReasons[ job ] << endl;
	//cout << "MASTER: Worker " << worker << " says: Constraint " << job << "     needed. Pending: "; printSet(setOfConstraintsPending);
	vectorOfConstraintsNeeded.push_back(job);
	if (!pending.empty()) {
	  int next = pending.front(); pending.pop();
	  MPI_Send(&next, 1, MPI_INT, worker, TAG_JOB, MPI_COMM_WORLD);
	  //cout << "Sent to worker " << worker << ": job " << next << endl;
	  active_workers++;
	}
      }
      else if (res == UNSAT) {
	setOfConstraintsPending.erase(job); 
	cout << "Not needed:  " << fixed<<setw(3)<<setfill(' ')<< job << endl;
	//cout << "MASTER: Worker " << worker << " says: Constraint " << job << " not needed. Pending: "; printSet(setOfConstraintsPending);
	for (int w = 1; w < world_size; ++w) MPI_Send(&job, 1, MPI_INT, w, TAG_INTERRUPT, MPI_COMM_WORLD);  // interrupt all workers
	
	// loop that receives interrupt confirmation from ALL workers and ignores other received messages:
	int numWorkersConfirmed = 0;
	while (numWorkersConfirmed != world_size-1) {
	  int imsg[2];
	  MPI_Recv(imsg, 2, MPI_INT, MPI_ANY_SOURCE, TAG_RESULT, MPI_COMM_WORLD, &st);
	  int iworker = st.MPI_SOURCE;
	  int ijob    = imsg[0];
	  int ires    = imsg[1];
	  if ( ires == INTERRUPTCONFIRMATION ) {
	    numWorkersConfirmed++;
	    //	    cout << "Master received from worker " << iworker << " confirmation of interruption of job " << ijob << endl;
	  }
	}
	//	cout << "Master received all confirmations " << endl;
	
	pending = {};
	for ( int c: setOfConstraintsPending ) pending.push(c);
	
	active_workers = 0;  	                // refill workers:
	for (int w = 1; w < world_size && !pending.empty(); ++w) {
	  int j = pending.front(); pending.pop();
	  MPI_Send(&j, 1, MPI_INT, w, TAG_JOB, MPI_COMM_WORLD);
	  active_workers++;
	  //cout << "Sent to worker " << w << ": job " << j << endl;
	}
      }
    
    }    
    for (int w = 1; w < world_size; ++w)  MPI_Send(nullptr, 0, MPI_INT, w, TAG_TERMINATE, MPI_COMM_WORLD);      // ---- terminate workers ----
}


void parse_command_line(int argc, char **argv) {
  for (int i = 1; i < argc; i++) {
    if (     argv[i][0] != '-'             ) { gcnfFile         = argv[i];                  } 
    else if (argv[i] == string("-proof")   ) { proofFile        = argv[++i];                }
    else if (argv[i] == string("-exp")     ) { explanationFile  = argv[++i];                }
    else if (argv[i] == string("-output")  ) { outFile          = argv[++i];                }
    else if (argv[i] == string("-fp")      ) { fpStrategy = 0;                              }
    else if (argv[i] == string("-times")   ) { fpStrategy = 1; fpTimes   = stoi(argv[++i]); }
    else if (argv[i] == string("-percent") ) { fpStrategy = 2; fpPercent = stoi(argv[++i]); }
    else if (argv[i] == string("-help")    ) {
      printHelp();
      MPI_Finalize();
      exit(0);
    }
  }
}


int main(int argc, char **argv)
{
  MPI_Init(&argc, &argv);
  int rank, size;
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  MPI_Comm_size(MPI_COMM_WORLD, &size);
  
  if (rank == 0) {
    cout << "Initialized MPI with one Master and " << size-1 << " Workers: ";  showWallClockTime();
    parse_command_line(argc,argv);
    readExplanationFile();  
    readExtendedClausesIntoTextBuffer();
  }
  
  MPI_Bcast( &inputBufferSize, 1, MPI_LONG, 0, MPI_COMM_WORLD);
  if (rank != 0) inputBuffer.resize(inputBufferSize);
  MPI_Bcast( inputBuffer.data(), inputBufferSize, MPI_CHAR, 0, MPI_COMM_WORLD);
  parseInputBufferIntoExtendedClauses(rank);

  if (rank == 0) {
    cout << "after reading input: ";  showWallClockTime();
    for (int i=0; i<numClauses; ++i) sort( extendedClauses[i].clause.begin(),  extendedClauses[i].clause.end() );
    for (int i=0; i<numClauses; ++i) constraintNumsOfClause[ extendedClauses[i].clause ].insert( extendedClauses[i].constraintNum );      
    // note: due to repeated clauses, this map may be smaller in size than numClauses
    fixpoint(fpStrategy,fpTimes,fpPercent);
    // cout << "after fixpoint: ";  showWallClockTime();
    computeHittingSet();  // find setOfConstraintsPending s.t, for each clause in clausesFixpoint, its constraint set is hit by it:
    // printSet(setOfConstraintsPending);
    clausesOfConstraint.resize(numConstraints);      
    for (int i=0; i<numClauses; ++i) {
       int c = extendedClauses[i].constraintNum;
       if ( setOfConstraintsPending.find(c) != setOfConstraintsPending.end() ) ; clausesOfConstraint[c].push_back(i);
    }
    cout << "First upper approximation (before trying to further reduce it): ";  showWallClockTime();    
    for ( int c: setOfConstraintsPending )
      cout<< fixed<<setw(4)<<setfill(' ')<< c <<" ("<<setw(7)<< clausesOfConstraint[c].size() <<" clauses) " << constraintReasons[c]<<endl;
    cout << endl;

    for ( int c: setOfConstraintsPending )  vectorOfConstraintsPending.push_back(c);
    numConstraintsPending = vectorOfConstraintsPending.size();    
  }

  MPI_Bcast( &numConstraintsPending, 1, MPI_INT, 0, MPI_COMM_WORLD);
  if (rank != 0) vectorOfConstraintsPending.resize(numConstraintsPending);
  MPI_Bcast( vectorOfConstraintsPending.data(), numConstraintsPending, MPI_INT, 0, MPI_COMM_WORLD);
  if (rank != 0) { for ( int c: vectorOfConstraintsPending ) setOfConstraintsPending.insert(c); }
  // if (rank==0) { cout << "after broadcast of data:  ";  showWallClockTime(); }

  // ===========  Main loops for Master and Workers:
  if (rank==0) cout << "Starting reduction with workers... " << endl; 
  if (rank==0) master(size); else worker(rank);

  if (rank==0) {  // =============== Final stuff for Master:
    cout << endl << "Done. Final MUS has " << vectorOfConstraintsNeeded.size() << " constraints: "<< endl;
    sort( vectorOfConstraintsNeeded.begin(),  vectorOfConstraintsNeeded.end() );
    int finalNumClauses=0;
    for ( int c: vectorOfConstraintsNeeded ) {
      finalNumClauses =+ clausesOfConstraint[c].size();
      cout<< fixed<<setw(4)<<setfill(' ')<< c <<" ("<<setw(7)<< clausesOfConstraint[c].size() <<" clauses) " << constraintReasons[c]<<endl;
    }
    cout << endl;    
    showWallClockTime();

    if ( outFile != "nullFile" ) {
      ofstream out(outFile.c_str());
      for ( int c: vectorOfConstraintsNeeded ) out << c << " ";
      out << endl;
      cout << "Final result written in " << outFile <<"." << endl;
    }
    // checkResultUnsatAndMinimality();    // checking result with solver for unsat and with muser2 for minimality
    // runWithMuser2();
  } 

  string rmAll = "rm -f " + timestampString + "*  muser2-output.gcnf tmp2";
  int status = system(rmAll.c_str());
  MPI_Finalize();
  return 0;
}


