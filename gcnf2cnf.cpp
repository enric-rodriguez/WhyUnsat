#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

int main(int argc, char **argv)
{
    std::ifstream in(argv[1]);
    if (!in) {
        std::cerr << "Error: cannot open infile.gcnf\n";
        return 1;
    }

    std::string line;
    int numVars = 0, numClauses = 0, numConstraints = 0;

    /* Read header */
    while (std::getline(in, line)) {
        if (line.empty() || line[0] == 'c')
            continue;

        std::istringstream iss(line);
        std::string p, format;
        iss >> p >> format >> numVars >> numClauses >> numConstraints;

        if (p == "p" && format == "gcnf") {
	  std::cout << "p cnf " << numVars << " " << numClauses << "\n";
	  break;
        } else {
	  std::cerr << "Error: invalid header line\n";
	  return 1;
        }
    }

    /* Read clauses */
    while (std::getline(in, line)) {
        if (line.empty() || line[0] == 'c')
            continue;

        /* Find end of { ... } block */
        std::size_t closeBrace = line.find('}');
        if (closeBrace == std::string::npos) {
            std::cerr << "Warning: skipping malformed clause line: "
                      << line << "\n";
            continue;
        }

        /* Everything after '}' contains the literals */
        std::string literalsPart = line.substr(closeBrace + 1);
	std::cout << literalsPart << "\n";
    }

    return 0;
}


