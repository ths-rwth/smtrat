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
	return os << op.parser.mOptions;
}
std::ostream& operator<<(std::ostream& os, SettingsPrinter sp) {
	for (const auto& option: sp.parser.mOptions.options()) {
		auto value = sp.parser.mValues[option->canonical_display_name()];
		os << option->canonical_display_name() << " = " << value.value() << std::endl;
	}
	return os;
}

}

SettingsParser::SettingsParser():
	mOptionsCore("Core settings"),
	mOptionsParser("Parser settings"),
	mOptionsSolver("Solver settings"),
	mOptionsValidation("Validation settings")
{
	mPositional.add("input-file", 1);

	auto& s = settings::Settings::getInstance();

	mOptionsCore.add_options()
		("help", po::bool_switch(&s.core.show_help))
		("info", po::bool_switch(&s.core.show_info))
		("version", po::bool_switch(&s.core.show_version))
		("settings", po::bool_switch(&s.core.show_settings))
		("cmake-options", po::bool_switch(&s.core.show_cmake_options))
		("license", po::bool_switch(&s.core.show_license))
	;
	mOptions.add(mOptionsCore);

	mOptionsParser.add_options()
		("dimacs", po::bool_switch(&s.parser.read_dimacs))
		("opb", po::bool_switch(&s.parser.read_opb))
		("input-file", po::value<std::string>(&s.parser.input_file))
	;
	mOptions.add(mOptionsParser);

	mOptionsSolver.add_options()
		("print-model", po::bool_switch(&s.solver.print_model))
		("print-all-models", po::bool_switch(&s.solver.print_all_models))
		("preprocess", po::bool_switch(&s.solver.preprocess))
		("pp-output-file", po::value<std::string>(&s.solver.preprocess_output_file))
		("statistics", po::bool_switch(&s.solver.print_statistics))
		("strategy", po::bool_switch(&s.solver.print_strategy))
		("timings", po::bool_switch(&s.solver.print_timings))
	;
	mOptions.add(mOptionsSolver);

	mOptionsValidation.add_options()
		("log-lemmata", po::bool_switch(&s.validation.log_lemmata))
		("log-theory-calls", po::bool_switch(&s.validation.log_theory_calls))
		("log-infeasible-subsets", po::bool_switch(&s.validation.log_infeasible_subsets))
		("log-filename", po::value<std::string>(&s.validation.log_filename)->default_value("validationlog.smt2"))
	;
	mOptions.add(mOptionsValidation);
}

bool SettingsParser::parse_options(int argc, char* argv[]) {
	argv_zero = argv[0];
	po::store(
		po::command_line_parser(argc, argv).options(mOptions).positional(mPositional).run(),
		mValues
	);
	po::notify(mValues);
	return true;
}

}