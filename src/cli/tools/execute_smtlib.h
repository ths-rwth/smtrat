#pragma once

#include "../parser/ParserWrapper.h"

#include "../CLIStatistics.h"

#include <string>

namespace smtrat {




template<typename Executor>
bool parseInput(const std::string& pathToInputFile, Executor& e, bool& queueInstructions) {
	if (pathToInputFile == "-") {
		queueInstructions = false;
		SMTRAT_LOG_DEBUG("smtrat", "Starting to parse from stdin");
		return smtrat::parseSMT2File(e, queueInstructions, std::cin);
	}

	std::ifstream infile(pathToInputFile);
	if (!infile.good()) {
		std::cerr << "Could not open file: " << pathToInputFile << std::endl;
		exit(SMTRAT_EXIT_NOSUCHFILE);
	}
	SMTRAT_LOG_DEBUG("smtrat", "Starting to parse " << pathToInputFile);
	return smtrat::parseSMT2File(e, queueInstructions, infile);
}

/**
 * Parse the file and save it in formula.
 * @param pathToInputFile The path to the input smt2 file.
 * @param formula A pointer to the formula object which holds the parsed input afterwards.
 * @param options Save options from the smt2 file here.
 */
template<typename Executor>
int executeFile(const std::string& pathToInputFile, Executor& e) {
#ifdef __WIN
//TODO: do not use magical number
#pragma comment(linker, "/STACK:10000000")
#else
	// Increase stack size to the maximum.
	rlimit rl;
	getrlimit(RLIMIT_STACK, &rl);
	rl.rlim_cur = rl.rlim_max;
	setrlimit(RLIMIT_STACK, &rl);
#endif

	SMTRAT_TIME_START(start);
	bool queueInstructions = true;
	if (!parseInput(pathToInputFile, e, queueInstructions)) {
		std::cerr << "Parse error" << std::endl;
		exit(SMTRAT_EXIT_PARSERFAILURE);
	}
	if (queueInstructions) {
		if (e.hasInstructions()) {
			SMTRAT_LOG_WARN("smtrat", "Running queued instructions.");
			e.runInstructions();
		} else {
			SMTRAT_LOG_WARN("smtrat", "Did not parse any instructions.");
		}
	}
	SMTRAT_TIME_FINISH(cli::statistics().parsing, start);
	return e.getExitCode();
}

}