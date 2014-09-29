/* 
 * File:   delta.cpp
 * Author: Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 *
 * Created on September 25, 2014, 4:12 PM
 */

#include <fstream>
#include <iostream>

#include "Manager.h"
#include "Parser.h"
#include "settings.h"

namespace bpo = boost::program_options;

int main(int argc, char* argv[]) {
	
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
	delta::Checker c(solver, temp, timeout, input);
	std::cout << "Original (" << n.complexity() << "):" << std::endl << n << std::endl;

	// Perform simplications.
	delta::Manager m(c, verbose);
	m.simplify(n);

	// Print result and store to file.
	std::cout << std::endl << "Result (" << n.complexity() << "):" << std::endl << n << std::endl;
	if (s.has("output-file")) {
		std::string output = s.as<std::string>("output-file");
		std::cout << "Writing to " << output << std::endl;
		std::ofstream out(output);
		out << n;
		out.close();
	}
	return 0;
}

