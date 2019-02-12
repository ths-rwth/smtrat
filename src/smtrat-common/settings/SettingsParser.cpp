#include "SettingsParser.h"

#include "Settings.h"

#include <boost/any.hpp>

namespace smtrat {
namespace settings {

std::ostream& operator<<(std::ostream& os, const boost::any& val) {
	if (val.empty()) {
		return os << "<empty>";
	} else if (boost::any_cast<bool>(&val)) {
		return os << std::boolalpha << boost::any_cast<bool>(val);
	} else if (boost::any_cast<std::string>(&val)) {
		return os << boost::any_cast<std::string>(val);
	}
	return os << "Unknown type";
}


std::ostream& operator<<(std::ostream& os, OptionPrinter op) {
	if (op.parser.argv_zero == nullptr) {
		os << "Usage: <binary> [options]";
	} else {
		os << "Usage: " << op.parser.argv_zero << " [options]";
	}
	for (unsigned i = 0; i < op.parser.mPositional.max_total_count(); ++i) {
		os << " " << op.parser.mPositional.name_for_position(i);
	}
	os << std::endl;
	return os << op.parser.mAllOptions;
}
std::ostream& operator<<(std::ostream& os, SettingsPrinter sp) {
	for (const auto& option: sp.parser.mAllOptions.options()) {
		auto value = sp.parser.mValues[option->canonical_display_name()];
		os << option->canonical_display_name() << " = " << value.value() << std::endl;
	}
	return os;
}

}

SettingsParser::SettingsParser() {
	mPositional.add("input-file", 1);

	auto& settings = settings::Settings::getInstance();

	{
		auto& s = settings.get<settings::CoreSettings>("core");
		add("Core settings").add_options()
			("help", po::bool_switch(&s.show_help), "show help")
			("info", po::bool_switch(&s.show_info), "show some basic information about this binary")
			("version", po::bool_switch(&s.show_version), "show the version of this binary")
			("settings", po::bool_switch(&s.show_settings), "show the settings that are used")
			("cmake-options", po::bool_switch(&s.show_cmake_options), "show the cmake options during compilation")
			("license", po::bool_switch(&s.show_license), "show the license")
		;
	}

	{
		auto& s = settings.get<settings::SolverSettings>("solver");
		add("Solver settings").add_options()
			("strategy", po::bool_switch(&s.print_strategy), "show the configured strategy")
			("preprocess", po::bool_switch(&s.preprocess), "only preprocess the input")
			("pp-output-file", po::value<std::string>(&s.preprocess_output_file), "store the preprocessed input to this file")
			("analyze-file", po::bool_switch(&s.analyze_file), "parse file and analyze it")
			("print-model", po::bool_switch(&s.print_model), "print a model if the input is satisfiable")
			("print-all-models", po::bool_switch(&s.print_all_models), "print all models of the input")
			("timings", po::bool_switch(&s.print_timings), "print timings after solving")
		;
	}

	{
		auto& s = settings.get<settings::ValidationSettings>("validation");
		add("Validation settings").add_options()
			("log-lemmata", po::bool_switch(&s.log_lemmata), "store all lemmata for validation")
			("log-theory-calls", po::bool_switch(&s.log_theory_calls), "store all theory calls for validation")
			("log-infeasible-subsets", po::bool_switch(&s.log_infeasible_subsets), "store all infeasible subsets for validation")
			("log-filename", po::value<std::string>(&s.log_filename)->default_value("validationlog.smt2"), "store the validation information in this file")
		;
	}
}

bool SettingsParser::parse_options(int argc, char* argv[]) {
	argv_zero = argv[0];
	po::store(
		po::command_line_parser(argc, argv).options(mAllOptions).positional(mPositional).run(),
		mValues
	);
	po::notify(mValues);
	return true;
}

}