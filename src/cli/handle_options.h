#pragma once

#include "config.h"
#include "ExitCodes.h"
#include "tools/compile_information.h"
#include <carl/util/CompileInfo.h>
#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/settings/Settings.h>

namespace smtrat {
namespace options_detail {

void print_cmake_options() {
	std::cout << "CMake options used for CArL:" << std::endl;
	std::cout << carl::CMakeOptions() << std::endl;
	std::cout << std::endl;
	std::cout << "CMake options used for SMT-RAT:" << std::endl;
	std::cout << smtrat::CMakeOptions() << std::endl;
}

void print_info() {
    std::cout << "Version: " << smtrat::compile_information::GitVersion << std::endl;
    std::cout << "Code is based on commit " << smtrat::compile_information::GitRevisionSHA1 << ". " << std::endl;
    std::cout << "Build type: " << smtrat::compile_information::BuildType << std::endl;
    std::cout << "Code was compiled with compiler " << smtrat::compile_information::CXXCompiler << " " << smtrat::compile_information::CXXCompilerVersion << std::endl;
    std::cout << "Build on a " << smtrat::compile_information::SystemName << " (" << compile_information::SystemVersion << ") machine." << std::endl;
}

void print_license() {
	std::string license = LICENSE_CONTENT;
	std::replace( license.begin(), license.end(), ';', '\n');
	std::cout << license << std::endl;
}

void print_version() {
	std::cout << compile_information::ProjectName << " " << compile_information::Version << std::endl;
	std::cout << compile_information::GitVersion << " based on " << compile_information::GitRevisionSHA1 << std::endl;
}

}

int handle_basic_options(const SettingsParser& parser) {
	if (settings_core().show_help) {
		std::cout << parser.print_help() << std::endl;
		return SMTRAT_EXIT_SUCCESS;
	}
	if (settings_core().show_info) {
		options_detail::print_info();
		return SMTRAT_EXIT_SUCCESS;
	}
	if (settings_core().show_version) {
		options_detail::print_version();
		return SMTRAT_EXIT_SUCCESS;
	}
	if (settings_core().show_settings) {
		std::cout << parser.print_options() << std::endl;
		return SMTRAT_EXIT_SUCCESS;
	}
	if (settings_core().show_cmake_options) {
		options_detail::print_cmake_options();
		return SMTRAT_EXIT_SUCCESS;
	}
	if (settings_core().show_license) {
		options_detail::print_license();
		return SMTRAT_EXIT_SUCCESS;
	}

	return SMTRAT_EXIT_UNDEFINED;
}

}