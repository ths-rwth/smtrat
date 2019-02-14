#pragma once

#include <iostream>
#include <string>

namespace smtrat {
	/**
	* Compile time generated information about compiler and system version.
	*/
	namespace compile_information {
		extern const std::string SystemName;
		extern const std::string SystemVersion;
		extern const std::string BuildType;
		extern const std::string CXXCompiler;
		extern const std::string CXXCompilerVersion;
		extern const std::string GitRevisionSHA1;
		extern const std::string PackageName;
		extern const std::string ProjectName;
		extern const std::string Version;
		extern const std::string Website;
		extern const std::string GitVersion;
	};

	struct CMakeOptionPrinter {
		bool advanced;
	};
	constexpr CMakeOptionPrinter CMakeOptions(bool advanced = false) noexcept {
		return { advanced };
	}
	std::ostream& operator<<(std::ostream& os, CMakeOptionPrinter cmop);
}
