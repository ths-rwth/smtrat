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
#include "../BenchmarkStatus.h"
#include "../Smt2Input.h"

namespace benchmax {

namespace fs = boost:: filesystem;

enum ToolInterface
{
	TI_SMTRAT, TI_OPENSMT, TI_Z3, TI_ISAT, TI_REDLOG_RLQE, TI_REDLOG_RLCAD, TI_QEPCAD, TI_INVALID
};

class Smt2Input;

class Tool {
protected:
	std::string mName;
	fs::path mBinary;
	std::string mArguments;
	std::map<std::string,std::string> mAttributes;
public:
	Tool(const std::string& name, const fs::path& binary, const std::string& arguments): mName(name), mBinary(binary), mArguments(arguments) {}

	std::string name() const {
		return mName;
	}
	
	fs::path binary() const {
		return mBinary;
	}
	
	virtual std::string getCommandline(const std::string& file) const {
		return mBinary.native() + " " + mArguments + " " + file;
	}
	virtual std::string getCommandline(const std::string& file, const std::string& localBinary) const {
		return localBinary + " " + mArguments + " " + file;
	}

	/**
	 * Checks if the file extension of the given path matches the given extension.
	 */
	bool isExtension(const fs::path& path, const std::string& extension) const {
		assert(fs::is_regular_file(path));
		return fs::extension(path) == extension;
	}
	virtual bool canHandle(const fs::path&) const {
		return false;
	}
	
	friend bool operator<(const Tool& lhs, const Tool& rhs) {
		return lhs.mBinary < rhs.mBinary;
	}
	
	virtual void additionalResults(const fs::path&, BenchmarkResults&) const {}
	

	
	private:
		ToolInterface	  mInterface;
		std::string		mPath;
		std::string		mExpectedSuffix;

	protected:
		/// If empty, no validation.
		std::string mValidationFilePath = "";
		fs::path	mFilePath;

		Tool(ToolInterface interface, const std::string& path, const std::string& expectedSuffix):
			mInterface(interface),
			mPath(path),
			mExpectedSuffix(expectedSuffix)
		{}

	public:
		virtual ~Tool(){}
		
		Tool(const Tool& t):
			mBinary(t.mBinary),
			mInterface(t.mInterface),
			mPath(t.mPath),
			mExpectedSuffix(t.mExpectedSuffix),
			mValidationFilePath(t.mValidationFilePath),
			mFilePath(t.mFilePath)
		{}
		Tool& operator=(const Tool& t) {
			mBinary = t.mBinary;
			mInterface = t.mInterface;
			mPath = t.mPath;
			mExpectedSuffix = t.mExpectedSuffix;
			mValidationFilePath = t.mValidationFilePath;
			mFilePath = t.mFilePath;
			return *this;
		}

		/**
		 * Constructs a string encoding the call to the tool, including arguments
		 * and the input.
		 * @param extraArguments	After the tool and the (standard) arguments, these arguments
		 *						  are inserted before the filepath comes. 
		 * @return The string which encodes the call
		 */
		virtual std::string getCallToTool(const std::string& extraArguments = "") const
		{
			return mPath + " " + " " + extraArguments + " " + mFilePath.string();
		}

		/**
		 * Gives, based on the output of the tool, an answer indicating errors or the result 
		 * the solver found.
		 * @param output
		 * @return 
		 */
		virtual BenchmarkResult getAnswer(const std::string& output) const
		{
			return extractAnswerFromOutput(output);
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
												const std::string& unknownIdentifier = "unknown") const;
};

inline std::ostream& operator<<(std::ostream& os, const Tool& tool) {
	return os << tool.binary().native();
}

}
