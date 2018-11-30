#pragma once

#include <boost/program_options.hpp>

#include <iostream>

namespace smtrat {
namespace po = boost::program_options;

class SettingsParser;

namespace settings {

struct OptionPrinter {
	const SettingsParser& parser;
};
std::ostream& operator<<(std::ostream& os, OptionPrinter);

struct SettingsPrinter {
	const SettingsParser& parser;
};
std::ostream& operator<<(std::ostream& os, SettingsPrinter);

}

class SettingsParser {
	friend std::ostream& settings::operator<<(std::ostream& os, settings::OptionPrinter);
	friend std::ostream& settings::operator<<(std::ostream& os, settings::SettingsPrinter);
private:
	char* argv_zero = nullptr;
	po::positional_options_description mPositional;
	po::options_description mOptionsCore;
	po::options_description mOptionsParser;
	po::options_description mOptionsSolver;
	po::options_description mOptionsValidation;
	po::options_description mOptions;
	po::variables_map mValues;
public:
	SettingsParser();

	bool parse_options(int argc, char* argv[]);

	settings::OptionPrinter print_help() const {
		return settings::OptionPrinter{*this};
	}

	settings::SettingsPrinter print_options() const {
		return settings::SettingsPrinter{*this};
	}
};

} // smtrat
