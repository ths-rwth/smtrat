/**
 * File:   Tool.h
 * @author Sebastian Junges
 * @author Ulrich Loup
 *
 * @since 2012-09-25
 * @version 2013-03-19
 */

#pragma once

#include <string>
#include <stdexcept>
#include <vector>
#include <boost/version.hpp>
#include <boost/filesystem.hpp>
#include "BenchmarkStatus.h"
#include "Smt2Input.h"

namespace fs = boost:: filesystem;

enum ToolInterface
{
	TI_SMTRAT, TI_OPENSMT, TI_Z3, TI_ISAT, TI_REDLOG_RLQE, TI_REDLOG_RLCAD, TI_QEPCAD, TI_INVALID
};

class Smt2Input;

class Tool
{
	private:
		const ToolInterface	  mInterface;
		const std::string		mPath;
		std::vector<std::string> mArguments;
		const std::string		mExpectedSuffix;

	protected:
		/// If empty, no validation.
		std::string mValidationFilePath = "";
		fs::path	mFilePath;

		Tool(ToolInterface interface, const std::string& path, const std::string& expectedSuffix):
			mInterface(interface),
			mPath(path),
			mArguments(),
			mExpectedSuffix(expectedSuffix)
		{}

	public:
		virtual ~Tool(){}

		/**
		 * 
		 * @param input A pointer to an object which encodes the input.
		 * @return false if something went wrong
		 */
		virtual bool convertInput(Smt2Input*)
		{
			return true;
		}

		/**
		 * Constructs a string encoding the call to the tool, including arguments
		 * and the input.
		 * @param extraArguments	After the tool and the (standard) arguments, these arguments
		 *						  are inserted before the filepath comes. 
		 * @return The string which encodes the call
		 */
		virtual std::string getCallToTool(const std::string& extraArguments = "")
		{
			return mPath + " " + arguments(' ') + " " + extraArguments + " " + mFilePath.string();
		}

		/**
		 * Gives, based on the output of the tool, an answer indicating errors or the result 
		 * the solver found.
		 * @param output
		 * @return 
		 */
		virtual BenchmarkResult getAnswer(const std::string& output)
		{
			return extractAnswerFromOutput(output);
		}

		/**
		 * The extension which indicates files that, either directly or after conversion,
		 * encode the input for the tool
		 * @return string for this extension, typically starting with a dot.
		 */
		std::string expectedFileExtension()
		{
			return mExpectedSuffix;
		}

		/**
		 * 
		 * @param validationFilePath
		 */
		virtual void setValidationFilePath(const std::string& validationFilePath)
		{
			mValidationFilePath = validationFilePath;
		}

		/**
		 * Set the path to the file which encodes the input.
		 * @param pathToInputFile
		 */
		void setFile(const fs::path& pathToInputFile)
		{
			mFilePath = pathToInputFile;
		}

		/**
		 * 
		 */
		ToolInterface toolInterface() const
		{
			return mInterface;
		}

		/**
		 * 
		 * @return Path to tool
		 */
		const std::string& path() const
		{
			return mPath;
		}

		/**
		 * 
		 * @param _seperator
		 * @return A string with all arguments, seperated by _seperator.
		 */
		std::string arguments(char _seperator) const
		{
			std::string result = "";
			for(std::vector<std::string>::const_iterator arg = mArguments.begin(); arg != mArguments.end(); ++arg)
			{
				result += _seperator + *arg;
			}
			return result;
		}

		virtual std::string interfaceToCommandString() const
		{
			switch(mInterface)
			{
				case TI_SMTRAT:
					return "-S ";
				case TI_Z3:
					return "-Z ";
				case TI_ISAT:
					return "-I ";
				case TI_REDLOG_RLCAD:
					return "-C ";
				case TI_REDLOG_RLQE:
					return "-R ";
				case TI_QEPCAD:
					return "-Q ";
				default:
					throw std::runtime_error("Command for tool interface is unknown.");
			}
		}

		/**
		 * Add a (standard) argument for the tool calls.
		 * @param _arg
		 */
		void addArgument(const std::string& _arg)
		{
			mArguments.push_back(_arg);
		}

	protected:
		/**
		 * Searches the relevant output of a tool for the three keys as well as some 
		 * keys indicating errors and returns an answer which encodes this.
		 * @param relevantOutput Part of the output which should be searched.
		 * @param satIdentifier	 A key for the sat-case. 
		 *						  The unsat-identifier may not be a substring of the sat-identifier.
		 * @param unsatIdentifier   A key for the unsat-case. 
		 * @param unknownIdentifier A key for the unknown-case.
		 * @return The result found in the output.
		 */
		BenchmarkResult extractAnswerFromOutput(const std::string& relevantOutput,
												const std::string& satIdentifier = "sat",
												const std::string& unsatIdentifier = "unsat",
												const std::string& unknownIdentifier = "unknown");
};

Tool* createTool(ToolInterface interface, const std::string& pathToTool);
