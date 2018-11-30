#pragma once

#include "config.h"
#include "ExitCodes.h"
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
    std::cout << "Version: " << smtrat::CompileInfo::GitVersion << std::endl;
    std::cout << "Code is based on commit " << smtrat::CompileInfo::GitRevisionSHA1 << ". " << std::endl;
    std::cout << "Build type:" << smtrat::CompileInfo::BuildType << std::endl;   
    std::cout << "Code was compiled with compiler " << smtrat::CompileInfo::CXXCompiler << " " << smtrat::CompileInfo::CXXCompilerVersion << std::endl;
    std::cout << "Build on a " << smtrat::CompileInfo::SystemName << " (" << CompileInfo::SystemVersion << ") machine." << std::endl;
}

void print_license() {
	std::string license = LICENSE_CONTENT;
	std::replace( license.begin(), license.end(), ';', '\n');
	std::cout << license << std::endl;
}

void print_timings(const smtrat::Manager& solver) {
	std::cout << "**********************************************" << std::endl;
	std::cout << "*                  Timings                   *" << std::endl;
	std::cout << "**********************************************" << std::endl;
	std::cout << "\t\tAdd \t\tCheck \t (calls) \tRemove" << std::endl;
	for (const auto& m: solver.getAllGeneratedModules()) {
		std::cout << m->moduleName() << ":\t";
		std::cout << m->getAddTimerMS() << "\t\t";
		std::cout << m->getCheckTimerMS() << "\t";
		std::cout << "(" << m->getNrConsistencyChecks() << ")\t\t";
		std::cout << m->getRemoveTimerMS() << std::endl;
	}
	std::cout << "**********************************************" << std::endl;
}

void print_version() {
	std::cout << CompileInfo::ProjectName << " " << CompileInfo::Version << std::endl;
	std::cout << CompileInfo::GitVersion << " based on " << CompileInfo::GitRevisionSHA1 << std::endl;
}

}

int handle_basic_options(const SettingsParser& parser) {
	const auto& settings = smtrat::Settings();

	if (settings.core.show_help) {
		std::cout << parser.print_help() << std::endl;
		return SMTRAT_EXIT_SUCCESS;
	}
	if (settings.core.show_info) {
		options_detail::print_info();
		return SMTRAT_EXIT_SUCCESS;
	}
	if (settings.core.show_version) {
		options_detail::print_version();
		return SMTRAT_EXIT_SUCCESS;
	}
	if (settings.core.show_settings) {
		std::cout << parser.print_options() << std::endl;
		return SMTRAT_EXIT_SUCCESS;
	}
	if (settings.core.show_cmake_options) {
		options_detail::print_cmake_options();
		return SMTRAT_EXIT_SUCCESS;
	}
	if (settings.core.show_license) {
		options_detail::print_license();
		return SMTRAT_EXIT_SUCCESS;
	}

	return SMTRAT_EXIT_UNDEFINED;
}

}