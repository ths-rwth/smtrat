/*
 * File:   BenchmarkTool.h
 * Author: Sebastian Junges
 *
 * Created on September 25, 2012, 12:10 PM
 */

#pragma once

#include "Tool.h"
#include <iostream>

namespace benchmax {
class Node;

struct BenchmarkTool
{
	static Tool*			   ValidationTool;
	static std::string		 assumptionsfile;
	static std::string		 TemporaryValidationResultFile;
	static std::string		 TemporaryAnswerFile;
	static std::string		 OutputDirectory;
	static std::string		 StatsXMLFile;
	static std::string		 RemoteOutputDirectory;
	static bool				UseStats;
	static bool				ProduceLatex;
	static std::string		 ExitMessage;
	static std::string		 PathOfBenchmarkTool;
	static std::string		 WrongResultPath;
	static std::vector<Node*>* Nodes;
	static unsigned			Timeout;
	static unsigned			Memout;
};

}