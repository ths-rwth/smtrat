/*
 * File:   BenchmarkTool.h
 * Author: Sebastian Junges
 *
 * Created on September 25, 2012, 12:10 PM
 */

#ifndef BENCHMARKTOOL_H
#define BENCHMARKTOOL_H

#include "Tool.h"
#include <iostream>

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
	static std::ostream		OStream;
	static std::string		 PathOfBenchmarkTool;
	static std::string		 WrongResultPath;
	static std::vector<Node*>* Nodes;
	static unsigned			Timeout;
	static unsigned			Memout;
};

#endif   /* TOOL_H */
