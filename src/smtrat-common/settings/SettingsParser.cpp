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
			("preprocess", po::bool_switch(&s.preprocess), "only preprocess the input (only available if compiled with corresponding CMake option)")
			("pp-output-file", po::value<std::string>(&s.preprocess_output_file), "store the preprocessed input to this file")
			("to-cnf-dimacs", po::bool_switch(&s.convert_to_cnf_dimacs), "transform formula to cnf as dimacs (only available if compiled with corresponding CMake option)")
			("to-cnf-smtlib", po::bool_switch(&s.convert_to_cnf_smtlib), "transform formula to cnf as smtlib (only available if compiled with corresponding CMake option)")
			("print-model", po::bool_switch(&s.print_model), "print a model if the input is satisfiable")
			("print-all-models", po::bool_switch(&s.print_all_models), "print all models of the input")
		;
	}

	{
		auto& s = settings.get<settings::ModuleSettings>("module");
		add("Module settings").add_options()
			("module.parameter", po::value<std::vector<std::string>>(&s.parameters), "add a parameter for modules (key=value)")
		;
	}
}

}