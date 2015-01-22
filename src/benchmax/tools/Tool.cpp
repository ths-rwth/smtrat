
#include "Tool.h"
#include "Z3Tool.h"
#include "smtratSolverTool.h"
#include "IsatTool.h"
#include "RedlogTool.h"
#include "QepcadTool.h"

namespace benchmax {

BenchmarkResult Tool::extractAnswerFromOutput(const std::string& relevantOutput,
											  const std::string& satIdentifier,
											  const std::string& unsatIdentifier,
											  const std::string& unknownIdentifier) const
{
	if(unknownIdentifier != "" && relevantOutput.find(unknownIdentifier) != std::string::npos)
	{
		assert(satIdentifier.find(unknownIdentifier) == std::string::npos);
		assert(unsatIdentifier.find(unknownIdentifier) == std::string::npos);
		return BR_UNKNOWN;
	}
	else if(unsatIdentifier != "" && relevantOutput.find(unsatIdentifier) != std::string::npos)
	{
		assert(satIdentifier.find(unsatIdentifier) == std::string::npos);
		return BR_UNSAT;
	}
	else if(satIdentifier != "" && relevantOutput.find(satIdentifier) != std::string::npos)
	{
		return BR_SAT;
	}
	return BR_NORESULT;
}

}
