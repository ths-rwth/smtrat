/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */


/**
 * @file   Benchmark.cpp
 * @author Sebastian Junges
 * @author Florian Corzilius
 * @author Ulrich Loup
 *
 * @since 2012-12-11
 * @version 2013-05-03
 */

#include "Benchmark.h"
#include "BenchmarkTool.h"
#include "BenchmarkStatus.h"
#include "config.h"
#include "Smt2Input.h"

namespace dt =boost:: date_time;
namespace pt =boost:: posix_time;
namespace ch =boost:: chrono;

#include <boost/filesystem.hpp>

using std::endl;
using std::string;
using carl::Formula;

/**
 *
 */
Benchmark::Benchmark():
	mPathToDirectory(""),
	mTool(NULL),
	mTimeout(150),
	mMemout(1000),
	mFilesList(),
	mResults(),
	mNrSolved(0),
	mNrSatSolved(0),
	mNrUnsatSolved(0),
	mNrSatInstances(0),
	mNrUnsatInstances(0),
	mAccumulatedTime(0),
	mVerbose(false),
	mQuiet(false),
	mMute(false),
	mProduceLaTeX(false),
	mStats(NULL),
	mTimeStamp("")
{
	mNextInstanceToTry = mFilesList.begin();
}

/**
 *
 * @param path
 * @param tool
 * @param timeout
 * @param verbose
 * @param quiet
 * @param mute
 * @param latex
 * @param _stats
 */
Benchmark::Benchmark(const string& path,
					 Tool* tool,
					 unsigned timeout,
					 unsigned memory,
					 bool verbose,
					 bool quiet,
					 bool mute,
					 bool latex,
					 Stats* const _stats):
	mPathToDirectory(path),
	mTool(tool),
	mTimeout(timeout),
	mMemout(memory),
	mNrSolved(0),
	mNrSatSolved(0),
	mNrUnsatSolved(0),
	mNrSatInstances(0),
	mNrUnsatInstances(0),
	mAccumulatedTime(0),
	mVerbose(verbose),
	mQuiet(quiet || mute),
	mMute(mute),
	mProduceLaTeX(latex),
	mStats(_stats),
	mTimeStamp("")
{
	mFilesList = pathlist();
	parseDirectory();
	mNextInstanceToTry = mFilesList.begin();
}

/**
 *
 */
Benchmark::~Benchmark(){}

/**
 * TODO not good, move this outside std.
 * @param out
 * @param rhs
 * @return
 */
namespace std
{
	ostream& operator <<(ostream& out, const pair<const string, const doublestring>& rhs)
	{
		out << rhs.first << ": " << rhs.second.second << "(" << rhs.second.first << ")";
		return out;
	}
}

/**
 *
 * @param _nrOfExamples
 * @return
 */
list<fs::path> Benchmark::pop(unsigned _nrOfExamples)
{
	list<fs::path> result = list<fs::path>();
	if(!done())
	{
		for(unsigned i = 0; i < _nrOfExamples; ++i)
		{
			result.push_back(*mNextInstanceToTry);
			++mNextInstanceToTry;
			if(done())
			{
				return result;
			}
		}
	}
	return result;
}

/**
 *
 * @return
 */
int Benchmark::run()
{
	//create timestamp.
	createTimestamp();
	mStats->addBenchmarkSet(benchmarkName());
	// Number of iterations.
	unsigned currFileCount = 0;
	//iterate over all files in the benchmark
	BOOST_FOREACH(fs::path pathToFile, mFilesList)
	{
		// Increase filecount
		currFileCount++;
		// Open in the stats a section for this benchmarkfile.
		mStats->addBenchmarkFile(pathToFile.stem().generic_string());
		// Tell the tool which file we are going to handle.
		mTool->setFile(pathToFile);
		// Print some info about the file to be handled next
		if(!mQuiet)
		{
			BenchmarkTool::OStream << "\r(" << currFileCount << "/" << mFilesList.size() << ")";
			BenchmarkTool::OStream.flush();
		}

		// Get an internal representation of the input.
		// This is only possible with a parser. Currently, we only support a parser for smt2.
		// Therefore, we check whether we have this parser available and the input
		// has an .smt2 suffix.
		BenchmarkStatus status;
#ifdef BENCHMAX_USE_SMTPARSER
		if(mTool->expectedFileExtension() == ".smt2")
		{
			// readSMT2Input also handles writing stats.
			status = readSMT2Input(pathToFile);
		}
		else
#endif
		{
			// No solver available or not an smt2 file.
			status = BS_UNKNOWN;
			mStats->addInputStat("status", benchmarkStatusToString(status));
		}
		// In case we use validation, we have to construct the validation file path.
		// And inform the tool about it.
		string assToCheckFileName = "";
		if(BenchmarkTool::ValidationTool != NULL)
		{
			assToCheckFileName = validationFilePath(pathToFile);
			mTool->setValidationFilePath(assToCheckFileName);
		}

		// Here, we open the run-specific part of the xml. Now the tool can write more info there.
		mStats->addRun(solverName(), mTimeout);

		// We make a system call starting the tool with the current input.
		std::string output = "";
		std::size_t		runningTime;
		int		 returnValue;
		systemCall(output, runningTime, returnValue);
		// After the call, we have to determine the response.
		BenchmarkResult answer = obtainResult(output, runningTime, returnValue, status);

		if(!mQuiet)
		{
			BenchmarkTool::OStream << "Returned: " << benchmarkResultToString(answer) << std::endl;
			BenchmarkTool::OStream << "**** The test took " << runningTime << " msec *********" << std::endl;
		}

		processResult(answer, status, runningTime, pathToFile, assToCheckFileName);
	}
	return 0;
}

/**
 *
 * @return
 */
int Benchmark::parseDirectory()
{
	fs::path p(mPathToDirectory);
	try
	{
		// does p actually exist?
		if(fs::exists(p))
		{
			// If it is a directory, we add all the contents
			if(fs::is_directory(p))
			{
				std::copy(fs::directory_iterator(p), fs::directory_iterator(), back_inserter(mFilesList));
				// Remove all files but those with the right extension.
				FilterFileExtensions filter = FilterFileExtensions(mTool->expectedFileExtension());
				mFilesList.remove_if(filter);
				mFilesList.sort();
				if(mVerbose)
				{
					BenchmarkTool::OStream << p << " is a directory containing:\n";
					std::copy(mFilesList.begin(), mFilesList.end(), std::ostream_iterator<fs::path>(BenchmarkTool::OStream, "\n"));
				}
			}
			// Not a directory, so (we assume?) it is a file.
			else
			{
				mFilesList.push_back(p);
			}
		}
		else if(!mMute)
			BenchmarkTool::OStream << p << " does not exist\n";
	}
	catch(const fs::filesystem_error& ex)
	{
		if(!mMute)
			BenchmarkTool::OStream << ex.what() << '\n';
		return 1;
	}
	return 0;
}

void Benchmark::createTimestamp()
{
	stringstream	timestamp;
	pt::time_facet* facet = new pt::time_facet("%Y%m%dT%H%M%S");
	timestamp.imbue(std::locale(timestamp.getloc(), facet));
	timestamp << pt::second_clock::local_time().date();
	mTimeStamp = timestamp.str();
}

void Benchmark::systemCall(std::string& callOutput, std::size_t& runningtime, int& returnValue)
{
	// First we construct the system call.
	stringstream call;
	// We limit the time and memory usage.
	call << "ulimit -S -t " << mTimeout << " && ulimit -S -v " << (mMemout * 1000);
	// And append the call to the tool.
	call << " && " << mTool->getCallToTool() << " ";

	//	std::cout << call.str() << std::endl;
	// Start a timer.
	ch::steady_clock::time_point start = ch::steady_clock::now();
	// Now we make the system call.
	FILE* pipe = popen(call.str().c_str(), "r");
	// Read output via pipe and look for termination of the calculation.
	// Get file content.
	callOutput = "";
	char buffer[255];
	while(!feof(pipe))
	{
		if(fgets(buffer, 255, pipe) != NULL)
		{
			callOutput += buffer;
		}
	}
	// Stop timing.
	ch::steady_clock::time_point end = ch::steady_clock::now();
	// Calculate difference (this value is returned)
	runningtime = (std::size_t)ch::round<ch::milliseconds>(end - start).count();
	if(mVerbose)
	{
		std::cout << callOutput << std::endl;
	}
	// Close the pipe.
	int retval = (pclose(pipe));
	// Determine exit status of the call.
	returnValue = WEXITSTATUS(retval);
}

ValidationResult Benchmark::validateResult(const std::string& inputFile, const std::string& validationFile)
{
	ValidationResult valResult = NOTVALIDATED;
	
	// First we construct the system call.
	stringstream call;
	// We limit the time and memory usage.
	call << "ulimit -S -t " << mTimeout << " && ulimit -S -v " << (mMemout * 1000);
	// And append the call to the tool.
	call << " && " << BenchmarkTool::ValidationTool->path() << " " << validationFile << " ";

	// Now we make the system call.
	FILE* pipe = popen( call.str().c_str(), "r" );
	
	if(!mQuiet)
	{
		BenchmarkTool::OStream << "Validating..";
		BenchmarkTool::OStream.flush();
	}
	
	// Get file content.v
	string searchPattern = "error";
	string callOutput = "";
	size_t callOutputSize = 0;
	bool errorOccurred = false;
	char buffer[255];
	while( !errorOccurred && !feof( pipe ) )
	{
		if( fgets( buffer, 255, pipe ) != NULL )
		{
			callOutput += buffer;
			if( callOutput.find( searchPattern, (callOutputSize > searchPattern.size() ? callOutputSize+1-searchPattern.size() : 0) ) != string::npos )
			{
				errorOccurred = true;
			}
			else
			{
				callOutputSize = callOutput.size();
			}
		}
	}
	
	pclose(pipe);
	
	if( errorOccurred )
	{
		valResult = FOUNDERROR;
		//errors occurred
		if(!mQuiet)
			BenchmarkTool::OStream << "Houston, we have a problem." << endl;
		//move assumptionsfile and benchmarkfile
		fs::path newloc = fs::path(BenchmarkTool::WrongResultPath);
		if(!fs::is_directory(newloc))
		{
			fs::create_directories(newloc);
		}
		newloc /= "wrong_results_" + solverName() + "_" + mTimeStamp + "/";
		if(!fs::is_directory(newloc))
		{
			fs::create_directories(newloc);
		}

		fs::path assumploc(BenchmarkTool::WrongResultPath + "wrong_results_" + solverName() + "_" + mTimeStamp + "/");

		assumploc /= "assumptions_" + inputFile;

		fs::copy(fs::path(validationFile), assumploc);
	}
	else
	{
		valResult = OKAY;
		if(!mQuiet)
			BenchmarkTool::OStream << "ok." << endl;
	}
	fs::remove(fs::path(validationFile));
	return valResult;
}

BenchmarkResult Benchmark::obtainResult(const std::string& output, std::size_t runningtime, int returnValue, BenchmarkStatus status)
{
	// Now we determine the given answer.
	// For that, there are multiple possibilities.
	// Case 1: The return value indicates some problem.
	switch(returnValue)
	{
		case 139:
			return BR_SEGFAULT;
		case 134:
			return BR_ABORT;
		case 152:
			return BR_TIMEOUT;
	}
	// Case 2: The runningtime is (almost) as high as the timeout
	if(runningtime > (mTimeout * 1000) - 20)
	{
		return BR_TIMEOUT;
	}
	// Case 3: We have to obtain the result from the output.
	// TODO (ticket: )
	// Get last line.
	stringstream sstream(output);
	string	   line, lineTmp;
	while(std::getline(sstream, lineTmp, '\n'))
	{
		if(!sstream.eof())
			line = lineTmp;
	}
	// Case 3A: ULimit returned some memory related stuff. This indicates a memory out.
	if(line.find("memory") != string::npos)
	{
		return BR_MEMOUT;
	}
	// Case 3B: We have one of the typical runtime error messages:
	if(line.find("error") != string::npos || line.find("ERROR") != string::npos || line.find("Error") != string::npos)
	{
		return BR_SOLVERERROR;
	}
	else if(line.find("Aborted") != string::npos && line.find("core dumped"))
	{
		return BR_UNEXPECTEDERROR;
	}
	else if(line.find("Assertion") != string::npos && line.find("failed") != string::npos)
	{
		return BR_UNEXPECTEDERROR;
	}
	// Case 3C: Tool related output should give more information.
	BenchmarkResult result = mTool->getAnswer(output);
	// if we have a known status for the input,
	// we check if the result is not wrong.
	if((result == BR_SAT && status == BS_UNSAT) || (result == BR_UNSAT && status == BS_SAT))
	{
		result = BR_WRONG;
	}
	return result;
}

#ifdef BENCHMAX_USE_SMTPARSER
BenchmarkStatus Benchmark::readSMT2Input(const fs::path& pathToFile)
{
	assert(mTool->expectedFileExtension() == ".smt2");
	Smt2Input* smt2Input = Smt2Input::initialize();
	// Parse the input
	smt2Input->parseSmtLib(pathToFile);
	// For some types of files, we have to internally transform the representation.
	mTool->convertInput(smt2Input);
	// Furthermore, some statistics are useful.
	smt2Input->extractInputStatistics(mStats);
	BenchmarkStatus status = smt2Input->getStatus();
	// We count the number of sat and unsat instances for some fast statistics output.
	if(status == BS_UNSAT)
	{
		mNrUnsatInstances++;
	}
	else if(status == BS_SAT)
	{
		mNrSatInstances++;
	}
	delete smt2Input;
	return status;
}
#endif

void Benchmark::processResult(BenchmarkResult answer,
							  BenchmarkStatus status,
							  std::size_t runningTime,
							  const fs::path& pathToFile,
							  const std::string& pathToValidationFile)
{
	ValidationResult valResult = NOTVALIDATED;
	// If the computation ran out of resources,
	// we simply report that and are done.
	if(answer == BR_TIMEOUT || answer == BR_MEMOUT)
	{
		mResults.push_back(std::pair<string, doublestring>(pathToFile.filename().generic_string(), doublestring("TO", "0")));
	}
	else if(answer == BR_NORESULT)
	{
		// Solver terminated without problems but gave no answer.
		mResults.push_back(std::pair<string, doublestring>(pathToFile.filename().generic_string(), doublestring("-", "0")));
	}
	else if(answer == BR_UNKNOWN)
	{
		
		mResults.push_back(pair<string, doublestring>(pathToFile.filename().generic_string(), doublestring("msec", boost::lexical_cast<string>(runningTime))));
	}
	else if(answer == BR_SAT || answer == BR_UNSAT)
	{
		// Solver terminates without problems.
		// We might validate intermediate steps of the solver.
		if(BenchmarkTool::ValidationTool != NULL)
		{
			valResult = validateResult(pathToFile.filename().string(), pathToValidationFile);
		}
		// If we do not know otherwise,
		// we assume the response was correct and add this to the report.
		if(valResult == NOTVALIDATED || valResult == OKAY)
		{
			mAccumulatedTime += runningTime;
			++mNrSolved;
			if(status == BS_SAT)
			{
				++mNrSatSolved;
			}
			else if(status == BS_UNSAT)
			{
				++mNrUnsatSolved;
			}

			mResults.push_back(
			pair<string, doublestring>(pathToFile.filename().generic_string(), doublestring("msec", boost::lexical_cast<string>(runningTime))));
		}
		else
		{
			answer = BR_WRONG;
		}
	}
	// All other cases except the one where the answer is wrong
	else if(answer != BR_WRONG)
	{
		mResults.push_back(std::pair<string, doublestring>(pathToFile.filename().generic_string(), doublestring("E", "0")));
	}

	// The case that the answer is wrong has to be a separate if block
	// As by validation, we might discover extra wrongs.
	if(answer == BR_WRONG)
	{
		mResults.push_back(std::pair<string, doublestring>(pathToFile.filename().generic_string(), doublestring("W", "0")));
	}

	// Before we proceed with the next file, we write the results of the run into our stats xml.
	mStats->addResult("runtime", mResults.back().second.first, mResults.back().second.second);
	mStats->addResult("answer", "", benchmarkResultToString(answer));
	mStats->addResult("validated", valResult != NOTVALIDATED);
}

/**
 *
 */
void Benchmark::printSettings() const
{
	if(mQuiet)
		return;
	BenchmarkTool::OStream << "+-" << std::endl;
	BenchmarkTool::OStream << "| Benchmark: " << benchmarkName() << std::endl;
	BenchmarkTool::OStream << "| Timeout: " << mTimeout << " seconds" << std::endl;
	BenchmarkTool::OStream << "| Solver: " << solverName() << std::endl;
	BenchmarkTool::OStream << "+-" << std::endl;
	BenchmarkTool::OStream << std::endl;
}

/**
 *
 */
void Benchmark::printResults() const
{
	if(mMute)
		return;
	BenchmarkTool::OStream << std::endl;
	BenchmarkTool::OStream << "**************************************************" << std::endl;
	BenchmarkTool::OStream << "Result: " << solverName() << " solved " << mNrSolved << " out of " << benchmarkCount() << std::endl;
	BenchmarkTool::OStream << "sat instances: " << mNrSatSolved << "/" << mNrSatInstances << ", unsat instances: " << mNrUnsatSolved << "/"
						   << mNrUnsatInstances << std::endl;
	BenchmarkTool::OStream << "Accumulated time: " << mAccumulatedTime << " msec" << std::endl;
	std::copy(mResults.begin(), mResults.end(), std::ostream_iterator<std::pair<string, doublestring> >(BenchmarkTool::OStream, "\n"));
	BenchmarkTool::OStream << "**************************************************" << endl << std::endl;
}
