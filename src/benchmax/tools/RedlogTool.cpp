/**
 * @file   RedlogTool.cpp
 *		 Created on April 14, 2013, 6:10 PM
 * @author: Sebastian Junges
 * @author: Ulrich Loup
 * @version 2013-04-25
 *
 */

#include <fstream>
#include <carl/formula/Formula.h>
#include "RedlogTool.h"

namespace benchmax {

ToolInterface redlogModeToToolInterface(RedlogMode mode)
{
	switch(mode)
	{
		case RLCAD:
			return TI_REDLOG_RLCAD;
		case RLQE:
			return TI_REDLOG_RLQE;
		default:
			return TI_INVALID;
	}
}

RedlogTool::RedlogTool(const std::string& pathToTool, RedlogMode mode):
	Tool(redlogModeToToolInterface(mode), pathToTool, ".smt2"),
	mMode(mode)
{}

std::string RedlogTool::getCallToTool(const std::string& extraArguments) const
{
	return Tool::getCallToTool(extraArguments + " < ");
}

BenchmarkResult RedlogTool::getAnswer(const std::string& output) const
{
	return extractAnswerFromOutput(output, "true", "false", "unknown"); // the "unknown" case never happens
}

#ifdef BENCHMAX_USE_SMTPARSER
#include <../src/solver/parser/Driver.h>
#include <../src/solver/ExitCodes.h>
bool RedlogTool::convertInput(Smt2Input* input)
{
	// switch from smt2 to Redlog file
	fs::path redlogFile = fs::path(BenchmarkTool::RemoteOutputDirectory + mFilePath.stem().generic_string() + ".red");
	mFilePath.swap(redlogFile);
	string formula  = input->getInputFormula()->toRedlogFormat();
	std::ofstream file;
	file.open( mFilePath.generic_string(), std::ios::out );
	file << "off echo$ load redlog$ rlset reals$ ";
	switch( mMode )
	{
	case RedlogMode::RLQE:
		file << "rlqe";
		break;
	case RedlogMode::RLCAD:
		file << "rlcad";
		break;
	}
	file << formula;
	file << ";";
	file.close();
	return true;
}
#endif

}