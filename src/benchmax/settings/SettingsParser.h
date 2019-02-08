#pragma once

#include <boost/program_options.hpp>
#include <carl/util/Singleton.h>
#include <filesystem>
#include <iostream>
#include <vector>

#include "Settings.h"

namespace std {

inline void validate(boost::any& v, const std::vector<std::string>& values, std::filesystem::path*, int) {
	namespace pov = boost::program_options::validators;
	namespace fs = std::filesystem;
	fs::path p(pov::get_single_string(values));
	if (fs::exists(p)) {
		v = fs::canonical(p);
	} else {
		v = fs::absolute(p);
	}
}

}

namespace benchmax {
namespace po = boost::program_options;

// Predeclaration.
class SettingsParser;

namespace settings {

/// Helper class to nicely print the options that are available.
struct OptionPrinter {
	/// Reference to parser.
	const SettingsParser& parser;
};
/// Streaming operator for a option printer.
std::ostream& operator<<(std::ostream& os, OptionPrinter);

/// Helper class to nicely print the settings that were parsed.
struct SettingsPrinter {
	/// Reference to parser.
	const SettingsParser& parser;
};
/// Streaming operator for a settings printer.
std::ostream& operator<<(std::ostream& os, SettingsPrinter);

}

/**
 * Generic class to manage settings parsing using boost::program_options.
 * Allows to register dynamically add new options_description object and manages parsing them from command line and config file.
 * When everything is registed finalize() has to be called to construct the full option description.
 */
class SettingsParser: public carl::Singleton<SettingsParser> {
	friend std::ostream& settings::operator<<(std::ostream& os, settings::OptionPrinter);
	friend std::ostream& settings::operator<<(std::ostream& os, settings::SettingsPrinter);
	friend carl::Singleton<SettingsParser>;
private:
	/// Stores the name of the current binary.
	char* argv_zero = nullptr;
	/// Stores the positional arguments.
	po::positional_options_description mPositional;
	/// Accumulates all available options.
	po::options_description mAllOptions;
	/// Stores the parsed values.
	po::variables_map mValues;
	/// Stores the individual options until the parser is finalized.
	std::vector<po::options_description> mOptions;
	/// Stores hooks for setting object finalizer functions.
	std::vector<std::function<void()>> mFinalizer;

	/// Default constructor.
	SettingsParser();

	/// Checks for unrecognized options that were found.
	void warn_for_unrecognized(const po::parsed_options& parsed) const;
	/// Parses the command line.
	void parse_command_line(int argc, char* argv[]);
	/// Parses the config file if one was configured.
	void parse_config_file();
	/// Calls the finalizer functions.
	void finalize_settings();
public:
	/// Finalizes the parser.
	void finalize() {
		for (const auto& po: mOptions)
			mAllOptions.add(po);
	}

	/**
	 * Adds a new options_description with a title and a reference to the settings object.
	 * The settings object is needed to pass it to the finalizer function.
	 */
	template<typename T>
	po::options_description& add(const std::string& title, T& options) {
		mOptions.emplace_back(po::options_description(title));
		mFinalizer.emplace_back([&options, this](){
			settings::finalize_settings(options, mValues);
		});
		return mOptions.back();
	}

	/// Parse the options.
	void parse_options(int argc, char* argv[]);

	/**
	 * Print a help page.
	 * Returns a helper object so that it can be used as follows:
	 *   std::cout << parser.print_help() << std::endl;
	 */
	settings::OptionPrinter print_help() const {
		return settings::OptionPrinter{*this};
	}

	/**
	 * Print the parsed settings.
	 * Returns a helper object so that it can be used as follows:
	 *   std::cout << parser.print_options() << std::endl;
	 */
	settings::SettingsPrinter print_options() const {
		return settings::SettingsPrinter{*this};
	}
};

} // smtrat
