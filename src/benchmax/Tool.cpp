
#include "Tool.h"
#include "tools/Z3Tool.h"
#include "tools/smtratSolverTool.h"
#include "tools/IsatTool.h"
#include "tools/RedlogTool.h"
#include "tools/QepcadTool.h"

Tool* createTool(ToolInterface interface, const std::string& pathToTool)
{
	switch(interface)
	{
		case TI_SMTRAT:
			return new SmtratSolverTool(pathToTool);
		case TI_Z3:
			return new Z3Tool(pathToTool);
		case TI_ISAT:
			return new IsatTool(pathToTool);
		case TI_REDLOG_RLCAD:
			return new RedlogTool(pathToTool, RLCAD);
		case TI_REDLOG_RLQE:
			return new RedlogTool(pathToTool, RLQE);
		case TI_QEPCAD:
			return new QepcadTool(pathToTool);
		default:
			throw std::runtime_error("Unknown tool interface.");
	}
}

BenchmarkResult Tool::extractAnswerFromOutput(const std::string& relevantOutput,
											  const std::string& satIdentifier,
											  const std::string& unsatIdentifier,
											  const std::string& unknownIdentifier)
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
