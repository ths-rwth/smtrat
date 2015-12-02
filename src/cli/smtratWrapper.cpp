/**
 * @file smtratSolver.cpp
 * @author Florian Corzilius
 * @author Sebastian Junges
 *
 * Created on May 04, 2012, 2:40 PM
 */

#ifndef __WIN
#include <sys/resource.h>
#endif
#include "ExitCodes.h"
#include "../lib/config.h"
#include "../lib/utilities/WrapperExternal.h"

unsigned executeWithWrapper(std::ifstream& infile) {
	smtrat::WrapperExternal* wrapper = smtrat::WrapperExternal::createWrapper("");
	std::string line;
	unsigned exitCode = SMTRAT_EXIT_UNEXPECTED_ANSWER;
	while(std::getline(infile, line))
	{
		if (line.find("(declare-fun ") != std::string::npos)
		{
			// declare
			// ignore
		}
		else if (line.find("; Add: ") != std::string::npos)
		{
			// add
			size_t pos = line.find(" with name: ");
			assert(pos != std::string::npos);
			std::string formula = line.substr(7, pos-7);
			std::string name = line.substr(pos+12, line.size()-pos-12);
			//std::cout << "Add: " << formula << " with name: " << name << std::endl;
			wrapper->add( formula.c_str(), name.c_str() );
		}
		else if (line.find("(assert ") != std::string::npos)
		{
			// add
			// ignore
		}
		else if (line.find("(check-sat)") != std::string::npos)
		{
			// check
			std::cout << "Check" << std::endl;
			switch (wrapper->check()) {
				case 0: {
					std::cout << "sat" << std::endl;
					exitCode = SMTRAT_EXIT_SAT;
					break;
				}
				case 1: {
					std::cout << "unsat" << std::endl;
					exitCode = SMTRAT_EXIT_UNSAT;
					break;
				}
				case 2: {
					std::cout << "unknown" << std::endl;
					exitCode = SMTRAT_EXIT_UNKNOWN;
					break;
				}
				default: {
					std::cerr << "unexpected output!";
					exitCode = SMTRAT_EXIT_UNEXPECTED_ANSWER;
					break;
				}
			}
		}
		else if (line.find("(push)") != std::string::npos)
		{
			// push
			wrapper->push();
		}
		else if (line.find("(pop)") != std::string::npos)
		{
			// pop
			wrapper->pop();
		}
		else if (line.find("; GetAllModels") != std::string::npos)
		{
			// get all models
			std::cout << "Get all models" << std::endl;
			char* buffer = new char[512];
			int size = wrapper->allModels(buffer, 512);
			if (size != 0)
			{
				char* buffer2 = new char[size];
				size = wrapper->allModels(buffer2, size);
				std::cout << "AllModels:" << std::endl << buffer2 << std::endl;
				delete[] buffer2;
			}
			else
			{
				std::cout << "AllModels:" << std::endl << buffer << std::endl;
			}
			delete[] buffer;
			assert(size == 0);
		}
		else if (line.find("; Add informationRelevantFormula: ") != std::string::npos)
		{
			// add informationRelevantFormula
			wrapper->addInformationRelevantFormula(line.substr(34).c_str());
		}
		else if (line.find("; Clear informationRelevantFormula") != std::string::npos)
		{
			// clear informationRelevantFormula
			wrapper->clearInformationRelevantFormula();
		}
		else if (line.find("; SetLemmaLevel to ") != std::string::npos)
		{
			// set lemmaLevel
			wrapper->setLemmaLevel(atoi(line.substr(19).c_str()));
		}
		else
		{
			// Not recognized
			std::cout << "Not recognized: " << line << std::endl;
		}
    }
	smtrat::WrapperExternal::disposeWrapper(wrapper);
	return exitCode;
}

int main( int argc, char* argv[] )
{
	//smtrat::testExpression();
/*#ifdef LOGGING
	if (!carl::logging::logger().has("smtrat")) {
		carl::logging::logger().configure("smtrat", "smtrat.log");
	}
	if (!carl::logging::logger().has("stdout")) {
		carl::logging::logger().configure("stdout", std::cout);
	}
	carl::logging::logger().filter("smtrat")
		("smtrat", carl::logging::LogLevel::LVL_INFO)
		("smtrat.module", carl::logging::LogLevel::LVL_TRACE)
		("smtrat.cad", carl::logging::LogLevel::LVL_DEBUG)
		("smtrat.preprocessing", carl::logging::LogLevel::LVL_DEBUG)
		("smtrat.sat", carl::logging::LogLevel::LVL_TRACE)
	;
	carl::logging::logger().filter("stdout")
		("smtrat", carl::logging::LogLevel::LVL_DEBUG)
		("smtrat.module", carl::logging::LogLevel::LVL_TRACE)
		("smtrat.parser", carl::logging::LogLevel::LVL_INFO)
		("smtrat.cad", carl::logging::LogLevel::LVL_DEBUG)
		("smtrat.preprocessing", carl::logging::LogLevel::LVL_DEBUG)
		("smtrat.sat", carl::logging::LogLevel::LVL_TRACE)
	;
#endif*/
	SMTRAT_LOG_INFO("smtrat", "Starting smtrat.");
    // This variable will hold the input file.
    std::string pathToInputFile = "";
	unsigned exitCode = 0;	
	
#ifdef __WIN
//TODO: do not use magical number
#pragma comment(linker, "/STACK:10000000")
#else
    // Increase stack size to the maximum.
	rlimit rl;
	getrlimit(RLIMIT_STACK, &rl);
	rl.rlim_cur = rl.rlim_max;
	setrlimit(RLIMIT_STACK, &rl);
#endif
	
	assert( argc == 2);
	pathToInputFile =  std::string(argv[1]);
	std::cout << pathToInputFile << std::endl;
	

	std::ifstream infile(pathToInputFile);
	if (!infile.good()) {
		std::cerr << "Could not open file: " << pathToInputFile << std::endl;
		exit(SMTRAT_EXIT_NOSUCHFILE);
	}
	
	exitCode = executeWithWrapper(infile);
    return (int)exitCode;
}
