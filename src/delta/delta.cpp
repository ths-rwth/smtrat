/* 
 * @file delta.cpp
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#include <chrono>
#include <fstream>
#include <iostream>

#include "Simplifier.h"
#include "Parser.h"
#include "settings.h"
#include "Executor.h"

namespace bpo = boost::program_options;
typedef std::chrono::system_clock Clock;
typedef std::chrono::seconds seconds;

int main(int argc, char* argv[]) {
	auto start = Clock::now();
	
	// Load settings.
	delta::Settings s;
	if (!s.load(argc, argv)) return 1;
	std::string input = s.as<std::string>("input-file");
	std::string solver = s.as<std::string>("solver");
	std::string temp = s.as<std::string>("temp-file");
	unsigned timeout = s.as<unsigned>("timeout");
	bool verbose = s.has("verbose");

	// Parse file.
	delta::Node n = delta::Parser::parse(input);
	// Initialize checker.
	delta::Checker c(solver, timeout, input);
	std::cout << "Original (" << n.complexity() << " nodes):" << std::endl << n << std::endl;

	// Perform simplications.
	delta::Simplifier simplifier(c, temp, verbose);
	simplifier(n);

	// Print result and store to file.
	std::cout << std::endl << "Result (" << n.complexity() << " nodes):" << std::endl << n << std::endl;
	if (s.has("output-file")) {
		std::string output = s.as<std::string>("output-file");
		std::cout << "Writing to " << output << std::endl;
		std::ofstream out(output);
		out << n;
		out.close();
	}

	std::cout << "This run took " << std::chrono::duration_cast<seconds>(Clock::now() - start).count() << " seconds." << std::endl;
	return 0;
}

