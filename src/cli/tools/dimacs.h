#pragma once

#include <smtrat-common/smtrat-common.h>

#include <carl/formula/parser/DIMACSImporter.h>

namespace smtrat {

template<typename Strategy>
int run_dimacs_file(Strategy& strategy, const std::string& filename) {
	carl::DIMACSImporter<Poly> dimacs(filename);
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