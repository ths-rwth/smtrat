/* 
 * File:   delta.cpp
 * Author: Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 *
 * Created on September 25, 2014, 4:12 PM
 */

#include <fstream>
#include <iostream>

#include <boost/program_options.hpp>

#include "Manager.h"
#include "Parser.h"

namespace bpo = boost::program_options;

int main(int argc, char* argv[]) {
	
	bpo::options_description desc("Allowed options");
	desc.add_options()
		("help,h", "produce help message")
		("input-file,i", bpo::value<std::string>()->required(), "input filename")
		("output-file,o", bpo::value<std::string>(), "output filename")
		("solver,s", bpo::value<std::string>()->default_value("./smtratSolver"), "solver executable")
		("temp-file,T", bpo::value<std::string>()->default_value(".delta.smt2"), "temporary filename")
		("timeout,t", bpo::value<unsigned>()->default_value(15), "timeout in seconds")
		("verbose,v", "be verbose")
	;
	bpo::positional_options_description pd;
	pd.add("input-file", 1);
	bpo::variables_map vm;
	try {
		bpo::store(bpo::command_line_parser(argc, argv).options(desc).positional(pd).run(), vm);
		if (vm.count("help")) {
			std::cout << desc << std::endl;
			return 0;
		}
		bpo::notify(vm);
	} catch(boost::program_options::required_option& e) {
		std::cerr << desc << std::endl;
		std::cerr << "ERROR: " << e.what() << std::endl << std::endl;
		return 1;
	} catch(boost::program_options::error& e) {
		std::cerr << desc << std::endl;
		std::cerr << "ERROR: " << e.what() << std::endl << std::endl;
		return 1;
	}
	
	std::string input = vm["input-file"].as<std::string>();
	std::string solver = vm["solver"].as<std::string>();
	std::string temp = vm["temp-file"].as<std::string>();
	unsigned timeout = vm["timeout"].as<unsigned>();
	bool verbose = vm.count("verbose") > 0;
	std::cout << "Reading from " << input << std::endl;
	std::cout << "Using timeout " << timeout << std::endl;
	
	delta::Node n = delta::Parser::parse(input);
	delta::Checker c(solver, temp, timeout, input);
	std::cout << "Original (" << n.complexity() << "):" << std::endl << n << std::endl;
	delta::Manager m(c, verbose);
	m.simplify(n);
	
	std::cout << std::endl << "Result (" << n.complexity() << "):" << std::endl << n << std::endl;
	if (vm.count("output-file")) {
		std::string output = vm["output-file"].as<std::string>();
		std::cout << "Writing to " << output << std::endl;
		std::ofstream out(output);
		out << n;
		out.close();
	}
	
	return 0;
}

