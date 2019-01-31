#pragma once

#include <boost/program_options.hpp>
#include <carl/util/Singleton.h>
#include <iostream>

#include "Settings.h"

namespace benchmax {
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

class SettingsParser: public carl::Singleton<SettingsParser> {
	friend std::ostream& settings::operator<<(std::ostream& os, settings::OptionPrinter);
	friend std::ostream& settings::operator<<(std::ostream& os, settings::SettingsPrinter);
	friend carl::Singleton<SettingsParser>;
private:
	char* argv_zero = nullptr;
	po::positional_options_description mPositional;
	po::options_description mAllOptions;
	po::variables_map mValues;

	std::vector<po::options_description> mOptions;
	std::vector<std::function<void()>> mFinalizer;
	SettingsParser();
public:

	void finalize() {
		for (const auto& po: mOptions)
			mAllOptions.add(po);
	}

	template<typename T>
	po::options_description& add(const std::string& title, T& options) {
		mOptions.emplace_back(po::options_description(title));
		mFinalizer.emplace_back([&options, this](){
			settings::finalize_settings(options, mValues);
		});
		return mOptions.back();
	}

	bool parse_options(int argc, char* argv[]);

	settings::OptionPrinter print_help() const {
		return settings::OptionPrinter{*this};
	}

	settings::SettingsPrinter print_options() const {
		return settings::SettingsPrinter{*this};
	}
};

} // smtrat
