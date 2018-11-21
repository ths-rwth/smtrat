#pragma once

#include <iostream>
#include <string>

namespace smtrat {
	/**
	* Compile time generated structure holding information about compiler and system version.
	*/
	struct CompileInfo {
		static const std::string SystemName;
		static const std::string SystemVersion;
		static const std::string BuildType;
		static const std::string CXXCompiler;
		static const std::string CXXCompilerVersion;
		static const std::string GitRevisionSHA1;
	};

	struct CMakeOptionPrinter {
		bool advanced;
	};
	constexpr CMakeOptionPrinter CMakeOptions(bool advanced = false) noexcept {
		return { advanced };
	}
	std::ostream& operator<<(std::ostream& os, CMakeOptionPrinter cmop);
}
