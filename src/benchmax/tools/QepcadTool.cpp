/**
 * @file   QepcadTool.cpp
 *		 Created on April 14, 2013, 6:09 PM
 * @author: Sebastian Junges
 * @author: Ulrich Loup
 * @version 2013-04-25
 *
 */
#include <unordered_map>
#include <fstream>
#include <carl/formula/Formula.h>
#include "QepcadTool.h"

namespace benchmax {

using std::string;
using std::unordered_map;

QepcadTool::QepcadTool(const std::string& pathToTool):
	Tool(TI_QEPCAD, pathToTool, ".smt2")
{}

std::string QepcadTool::getCallToTool(const std::string& extraArguments)
{
	return Tool::getCallToTool(extraArguments + " < ");
}

BenchmarkResult QepcadTool::getAnswer(const std::string& output)
{
	return extractAnswerFromOutput(output, "TRUE", "FALSE", "UNKNOWN"); // the "UNKNOWN" case never happens
}

#ifdef BENCHMAX_USE_SMTPARSER
#include <ginac/ginac.h>
#include <../src/solver/parser/Driver.h>
#include <../src/solver/ExitCodes.h>
bool QepcadTool::convertInput(Smt2Input* input)
{
	// switch from smt2 to QEPCAD file / mFilePath.replace_extension(".cad");
	fs::path qepcadFile = fs::path(BenchmarkTool::RemoteOutputDirectory + mFilePath.stem().generic_string() + ".cad");
	mFilePath.swap(qepcadFile);
	// map variables to renamed variable ids
	std::unordered_map<string, string>	variableIds = std::unordered_map<string, string>();
	const GiNaC::symtab& realValuedVars = Formula::constraintPool().realVariables(); // input.first->realValuedVars();
	const std::set< std::string >& booleanVars = Formula::constraintPool().booleanVariables();// input.first->booleanVars();
	unsigned										x = 0; // real variable counter
	unsigned										y = 0; // Boolean variable counter
	for( GiNaC::symtab::const_iterator i = realValuedVars.begin(); i != realValuedVars.end(); ++i )
	{
		std::stringstream xStr;
		xStr << x;
		++x;
		variableIds[ i->first ] = "r" + xStr.str();
//					cout << "Mapping " << i->first << " -> " << variableIds[ i->first ] << endl;
	}
	for( std::set< std::string >::const_iterator j = booleanVars.begin(); j != booleanVars.end(); ++j )
	{
		std::stringstream yStr;
		yStr << y;
		++y;
		variableIds[ *j ] = "b" + yStr.str();
//				cout << "Mapping " << *j << " -> " << variableIds[ *j ] << endl;
	}
	string formula  = input->getInputFormula()->toQepcadFormat( ( x>0 || y>0 ), variableIds );
	std::ofstream file;
	file.open(mFilePath.generic_string(), std::ios::out);
	file << "[" << mFilePath.filename().string() << "]" << std::endl << formula << std::endl << "finish" << std::endl << std::endl;
	file.close();
	return true;
}
#endif

}