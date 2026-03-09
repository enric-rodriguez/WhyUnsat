
all: WhyUnsat gcnf2cnf

WhyUnsat:	WhyUnsat.cpp
		mpic++ -O3 WhyUnsat.cpp -o WhyUnsat

gcnf2cnf:	gcnf2cnf.cpp
		g++ -O3 -Wall gcnf2cnf.cpp -o gcnf2cnf

clean:
	rm -f WhyUnsat gcnf2cnf infile.gcnf CPproof.proof constraintMessages.txt job_*.cnf WhyUnsatResult.gcnf header_* clauses_* proof.proof tmpClauses.cnf symbolicModel kissatCheck.cnf *.exe
