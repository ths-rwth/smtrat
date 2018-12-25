#pragma once

#include <smtrat-common/smtrat-common.h>

#include <carl/formula/parser/OPBImporter.h>

namespace smtrat {

template<typename Strategy>
int run_opb_file(Strategy& strategy, const std::string& filename) {
	carl::OPBImporter<Poly> opb(filename);
	SMTRAT_LOG_INFO("smtrat", "Parsing " << filename << " using OPB");
	int exitCode = 0;
	auto input = opb.parse();
	if (!input) {
		SMTRAT_LOG_ERROR("smtrat", "Parsing " << filename << " failed.");
		exitCode = SMTRAT_EXIT_UNKNOWN;
	} else {
		SMTRAT_LOG_INFO("smtrat", "Parsed " << input->first);
		SMTRAT_LOG_INFO("smtrat", "with objective " << input->second);
		if (!input->second.isConstant()) {
			strategy.addObjective(input->second, true);
		}
		strategy.add(input->first);
		switch (strategy.check()) {
			case smtrat::Answer::SAT: {
				std::cout << "sat" << std::endl;
				exitCode = SMTRAT_EXIT_SAT;
				break;
			}
			case smtrat::Answer::UNSAT: {
				std::cout << "unsat" << std::endl;
				exitCode = SMTRAT_EXIT_UNSAT;
				break;
			}
			case smtrat::Answer::UNKNOWN: {
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
	}
	return exitCode;
}

}