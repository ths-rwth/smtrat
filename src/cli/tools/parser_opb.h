#pragma once

#include "config.h"

#include <smtrat-common/smtrat-common.h>
#include <smtrat-optimization/smtrat-optimization.h>

#ifdef CLI_ENABLE_OPB_PARSER

#include <carl-io/OPBImporter.h>


namespace smtrat {

template<typename Strategy>
int run_opb_file(Strategy& strategy, const std::string& filename) {
	Optimization<Strategy> optimization(strategy);
	carl::io::OPBImporter<Poly> opb(filename);
	SMTRAT_LOG_INFO("smtrat", "Parsing " << filename << " using OPB");
	int exitCode = 0;
	auto input = opb.parse();
	if (!input) {
		SMTRAT_LOG_ERROR("smtrat", "Parsing " << filename << " failed.");
		exitCode = SMTRAT_EXIT_UNKNOWN;
	} else {
		SMTRAT_LOG_INFO("smtrat", "Parsed " << input->first);
		SMTRAT_LOG_INFO("smtrat", "with objective " << input->second);
		strategy.add(input->first);
		if (!input->second.is_constant()) {
			optimization.add_objective(input->second, true);
			exitCode = handleAnswer(std::get<0>(optimization.compute()));
		} else {
			exitCode = handleAnswer(strategy.check());
		}
	}
	return exitCode;
}

int handleAnswer(Answer a) {
	switch (a) {
		case smtrat::Answer::SAT:
		case smtrat::Answer::OPTIMAL: {
			std::cout << "sat" << std::endl;
			return SMTRAT_EXIT_SAT;
			break;
		}
		case smtrat::Answer::UNSAT: {
			std::cout << "unsat" << std::endl;
			return SMTRAT_EXIT_UNSAT;
			break;
		}
		case smtrat::Answer::UNKNOWN: {
			std::cout << "unknown" << std::endl;
			return SMTRAT_EXIT_UNKNOWN;
			break;
		}
		default: {
			std::cerr << "unexpected output!";
			return SMTRAT_EXIT_UNEXPECTED_ANSWER;
			break;
		}
	}
}

}

#else

namespace smtrat {

template<typename Strategy>
int run_opb_file(Strategy&, const std::string&) {
	SMTRAT_LOG_ERROR("smtrat", "This version of SMT-RAT was compiled without support for OPB parsing. Please enable it by setting the corresponding CMake option.");
	return 0;
}

}

#endif