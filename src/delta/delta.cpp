/* 
 * @file delta.cpp
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#include <chrono>
#include <fstream>
#include <iostream>

#include "Producer.h"
#include "Parser.h"
#include "Settings.h"
#include "Consumer.h"

namespace bpo = boost::program_options;
typedef std::chrono::system_clock Clock;
typedef std::chrono::seconds seconds;

int main(int argc, char* argv[]) {
	auto start = Clock::now();
	
	// Load settings.
	delta::Settings s(argv[0]);
	if (!s.load(argc, argv)) return 1;
	std::string input = s.as<std::string>("input-file");
	std::string solver = s.as<std::string>("solver");
	std::string temp = s.as<std::string>("temp-file");
	unsigned timeout = s.as<unsigned>("timeout");

	// Parse file.
	delta::Node n;
	if (!delta::Parser::parse(input, n)) return 1;
	unsigned originalSize = n.complexity();

	// Initialize checker.
	std::cout << "Calculating original exit code..." << std::endl;
	delta::Checker c(solver, timeout, input);
	std::cout << BGREEN << "Original exit code is " << c.expectedCode() << END << std::endl;
	if (s.has("verbose")) {
		std::cout << "Original (" << n.complexity() << " nodes):" << std::endl << n << std::endl;
	}

	// Perform simplications.
	delta::Producer producer(c, temp, s);
	unsigned iterations = producer(n);

	// Print result and store to file.
	if (s.has("verbose")) {
		std::cout << std::endl << "Result (" << n.complexity() << " nodes):" << std::endl << n << std::endl;
	} else {
		std::cout << std::endl << "Reduced from " << originalSize << " to " << n.complexity() << " nodes." << std::endl;
	}
	if (s.has("output-file")) {
		std::string output = s.as<std::string>("output-file");
		std::cout << "Writing to " << output << std::endl;
		std::ofstream out(output);
		out << n;
		out.close();
	}

	std::cout << "This run took " << std::chrono::duration_cast<seconds>(Clock::now() - start).count() << " seconds for " << iterations << " iterations." << std::endl;
	return 0;
}

