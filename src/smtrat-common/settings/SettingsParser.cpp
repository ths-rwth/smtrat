#include "SettingsParser.h"

#include "Settings.h"

namespace smtrat {

namespace po = boost::program_options;

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
			("strategy", po::bool_switch(&s.show_strategy), "show the configured strategy")
			("license", po::bool_switch(&s.show_license), "show the license")
			("config,c", po::value<std::string>(&s.config_file), "load config from the given config file")
		;
	}

	{
		auto& s = settings.get<settings::SolverSettings>("solver");
		add("Solver settings").add_options()
			("preprocess", po::bool_switch(&s.preprocess), "only preprocess the input")
			("pp-output-file", po::value<std::string>(&s.preprocess_output_file), "store the preprocessed input to this file")
			("to-cnf-dimacs", po::bool_switch(&s.convert_to_cnf_dimacs), "transform formula to cnf as dimacs")
			("to-cnf-smtlib", po::bool_switch(&s.convert_to_cnf_smtlib), "transform formula to cnf as smtlib")
			("print-model", po::bool_switch(&s.print_model), "print a model if the input is satisfiable")
			("print-all-models", po::bool_switch(&s.print_all_models), "print all models of the input")
			("timings", po::bool_switch(&s.print_timings), "print timings after solving")
		;
	}

	{
		auto& s = settings.get<settings::ValidationSettings>("validation");
		add("Validation settings").add_options()
			("log.lemmata", po::bool_switch(&s.log_lemmata), "store all lemmata for validation")
			("log.theory-calls", po::bool_switch(&s.log_theory_calls), "store all theory calls for validation")
			("log.infeasible-subsets", po::bool_switch(&s.log_infeasible_subsets), "store all infeasible subsets for validation")
			("log.filename", po::value<std::string>(&s.log_filename)->default_value("validationlog.smt2"), "store the validation information in this file")
		;
	}
}

}