/**
 * @file Execute.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

namespace benchmax {

inline int callProgram(const std::string& commandline, std::string& stdout, bool print_to_stdout = false) {
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