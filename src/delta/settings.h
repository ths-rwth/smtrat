/**
 * @file settings.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <cassert>

#include <boost/program_options.hpp>

#include "Simplifier.h"

namespace bpo = boost::program_options;

namespace delta {

/**
 * This class loads and checks the command line options with help of `boost::program_options`.
 */
class Settings {
	/// Parsed options.
	bpo::variables_map vm;
public:
	/**
	 * Load options from command line.
	 * @param argc Number of arguments.
	 * @param argv Content of arguments.
	 */
	bool load(int argc, char* argv[]) {
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
		try {
			bpo::store(bpo::command_line_parser(argc, argv).options(desc).positional(pd).run(), vm);
			if (vm.count("help")) {
				std::cout << desc << std::endl;
				return false;
			}
			bpo::notify(vm);
		} catch(boost::program_options::required_option& e) {
			std::cerr << desc << std::endl;
			std::cerr << "ERROR: " << e.what() << std::endl << std::endl;
			return false;
		} catch(boost::program_options::error& e) {
			std::cerr << desc << std::endl;
			std::cerr << "ERROR: " << e.what() << std::endl << std::endl;
			return false;
		}
		return true;
	}
	/**
	 * Get option with given name as a given type.
	 * If there is no such option of it has a different type, exceptions may be thrown.
     * @param s Name of the option.
     * @return Value of the option as type T.
     */
	template<typename T>
	T as(const std::string& s) {
		assert(has(s));
		return vm[s].as<T>();
	}
	/**
	 * Checks if there is an option with this name.
     * @param s Name of the option.
     * @return If option was set.
     */
	bool has(const std::string& s) {
		return vm.count(s) > 0;
	}
};

}