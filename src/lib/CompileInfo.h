#include <string>

namespace smtrat
{
	/**
	* Compile time generated structure holding information about compiler and system version.
	*/
	struct CompileInfo
	{
		static const std::string SystemName;
		static const std::string SystemVersion;
		static const std::string BuildType;
		static const std::string CXXCompiler;
	};
}
