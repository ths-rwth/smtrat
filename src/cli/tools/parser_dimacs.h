#pragma once

#include "config.h"
#include <smtrat-common/smtrat-common.h>

#ifdef CLI_ENABLE_DIMACS_PARSER
#include <carl-io/DIMACSImporter.h>

namespace smtrat {

template<typename Strategy>
int run_dimacs_file(Strategy& strategy, const std::string& filename) {
	carl::io::DIMACSImporter<Poly> dimacs(filename);
	int exitCode = 0;
	while (dimacs.hasNext()) {
		strategy.add(dimacs.next());
		switch (strategy.check()) {
			case Answer::SAT: {
				std::cout << "sat" << std::endl;
				exitCode = SMTRAT_EXIT_SAT;
				break;
			}
			case Answer::UNSAT: {
				std::cout << "unsat" << std::endl;
				exitCode = SMTRAT_EXIT_UNSAT;
				break;
			}
			case Answer::UNKNOWN: {
				std::cout << "unknown" << std::endl;
				exitCode = SMTRAT_EXIT_UNKNOWN;
				break;
			}
			default: {
				std::cerr << "unexpected output!";
				exitCode = SMTRAT_EXIT_UNEXPECTED_ANSWER;
				break;
			}
		}
		if (dimacs.hasNext()) strategy.reset();
	}
	return exitCode;
}

}

#else

namespace smtrat {

template<typename Strategy>
int run_dimacs_file(Strategy&, const std::string&) {
	SMTRAT_LOG_ERROR("smtrat", "This version of SMT-RAT was compiled without support for DIMACS parsing. Please enable it by setting the corresponding CMake option.");
	return 0;
}

}

#endif