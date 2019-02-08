/**
 * @file Execute.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

namespace benchmax {

/**
 * Runs an external program from some command line and records the output to stdout.
 * Prints the program output and records it at the same time if print_to_stdout is set to true.
 * @param commandline Program to execute.
 * @param stdout Standard output.
 * @param print_to_stdout Also print if true.
 * @return Exit code of the program.
 */
inline int call_program(const std::string& commandline, std::string& stdout, bool print_to_stdout = false) {
	FILE* pipe = popen(commandline.c_str(), "r");
	char buf[255];
	while (!feof(pipe)) {
		if (fgets(buf, sizeof(buf), pipe) != nullptr) {
			stdout += buf;
			if (print_to_stdout) {
				std::cout << buf;
			}
		}
	}
	return pclose(pipe);
}

}