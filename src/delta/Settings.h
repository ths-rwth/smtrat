/**
 * @file settings.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <cassert>
#include <iostream>

#include "../cli/config.h"
#ifdef __VS
#pragma warning(push, 0)
#include <boost/program_options.hpp>
#pragma warning(pop)
#else
#include <boost/program_options.hpp>
#endif

namespace bpo = boost::program_options;

namespace delta {

/**
 * This class loads and checks the command line options with help of `boost::program_options`.
 */
class Settings {
	/// Name of this executable
	std::string executable;
	/// Parsed options.
	bpo::variables_map vm;
	/// Options description.
	bpo::options_description desc;
	/// Positional options description
	bpo::positional_options_description pd;
public:
	/**
	 * Constructor.
     * @param executable Name of this binary.
     */
	Settings(const std::string& executable): executable(executable), desc("General options") {
		desc.add_options()
			("help,h", "produce help message")
			("input-file,i", bpo::value<std::string>()->required(), "input filename")
			("output-file,o", bpo::value<std::string>()->default_value("delta.out.smt2"), "output filename")
			("solver,s", bpo::value<std::string>()->default_value("./smtrat"), "solver executable")
			("memout,m", bpo::value<std::size_t>()->default_value(1024), "memout in megabytes")
			("timeout,t", bpo::value<std::size_t>()->default_value(15), "timeout in seconds")
			("verbose,v", "be verbose")
		;
		bpo::options_description finetuning("Finetuning");
		finetuning.add_options()
			("dfs", "use DFS instead of BFS")
			("delay-declare-fun", bpo::value<bool>()->default_value(true), "delay removal of declare-fun")
			("temp-file", bpo::value<std::string>()->default_value(".delta.smt2"), "temporary filename")
			("skip", bpo::value<std::size_t>()->default_value(0), "skip the first n nodes")
			("threads", bpo::value<std::size_t>()->default_value(0), "number of parallel threads")
		;
		bpo::options_description operators("Node operators");
		operators.add_options()
			("no-children", "Disable replacement by children")
			("no-merge", "Disable merging with children")
			("no-constants", "Disable replacement by constants")
			("no-numbers", "Disable simplification of numbers")
			("no-lets", "Disable elimination of let expressions")
			("no-removal", "Disable removal")
		;
		desc.add(finetuning).add(operators);
		pd.add("input-file", 1);
	}
	
	/**
	 * Streaming operator.
     * @param os Output stream.
     * @param s Settings.
     * @return os.
     */
	friend std::ostream& operator<<(std::ostream& os, const Settings& s) {
		return os << "Usage: " << s.executable << " [options] <input-file>" << std::endl << s.desc << std::endl;
	}
	
	/**
	 * Load options from command line.
	 * @param argc Number of arguments.
	 * @param argv Content of arguments.
	 */
	bool load(int argc, char* argv[]) {
		try {
			bpo::store(bpo::command_line_parser(argc, argv).options(desc).positional(pd).run(), vm);
			if (vm.count("help")) {
				std::cout << *this;
				return false;
			}
			bpo::notify(vm);
		} catch(boost::program_options::required_option& e) {
			std::cerr << *this << std::endl << "ERROR: " << e.what() << std::endl << std::endl;
			return false;
		} catch(boost::program_options::error& e) {
			std::cerr << *this << std::endl << "ERROR: " << e.what() << std::endl << std::endl;
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
	const T& as(const std::string& s) const {
		assert(has(s));
		return vm[s].as<T>();
	}
	/**
	 * Set option with given name as a given type.
	 * If there is no such option exceptions may be thrown.
     * @param s Name of the option.
     * @param t New value.
     */
	template<typename T>
	void set(const std::string& s, const T& t) {
		assert(has(s));
		vm.at(s).value() = t;
	}
	/**
	 * Checks if there is an option with this name.
     * @param s Name of the option.
     * @return If option was set.
     */
	bool has(const std::string& s) const {
		return vm.count(s) > 0;
	}
	/**
	 * Check if the option with the given name was set due to its default value.
	 * If there is no such option exceptions may be thrown.
     * @param s Name of the option.
     * @return Whether it's value was set as the default.
     */
	bool isDefault(const std::string& s) const {
		assert(has(s));
		return vm[s].defaulted();
	}
};

}
