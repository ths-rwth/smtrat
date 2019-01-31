/**
 * File:   Tool.h
 * @author Sebastian Junges
 * @author Ulrich Loup
 *
 * @since 2012-09-25
 * @version 2013-03-19
 */

#pragma once

#include <filesystem>
#include <functional>
#include <string>
#include <stdexcept>
#include <vector>

#include <boost/functional/hash.hpp>
#include <boost/version.hpp>

#include <benchmax/results/BenchmarkResult.h>
#include <benchmax/benchmarks/BenchmarkSet.h>
#include <benchmax/settings/Settings.h>

namespace benchmax {

namespace fs = std::filesystem;

class Tool {
protected:
	std::string mName;
	fs::path mBinary;
	std::string mArguments;
	std::map<std::string,std::string> mAttributes;
public:
	Tool() = delete;
	Tool(const Tool&) = delete;
	Tool(Tool&&) = delete;
	Tool(const fs::path& binary, const std::string& arguments): Tool("Generic", binary, arguments) {}
	Tool(const std::string& name, const fs::path& binary, const std::string& arguments): mName(name), mBinary(binary), mArguments(arguments) {}
	
	virtual ~Tool() = default;
	Tool& operator=(const Tool&) = delete;
	Tool& operator=(Tool&&) = delete;

	/// Common name of this tool.
	std::string name() const {
		return mName;
	}
	
	/// Full path to the binary.
	fs::path binary() const {
		return mBinary;
	}
	
	/// A set of attributes, for example compilation options.
	const std::map<std::string,std::string>& attributes() const {
		return mAttributes;
	}
	
	/// Hash of the attributes.
	std::size_t attributeHash() const {
		std::size_t res = 0;
		for (const auto& it: mAttributes) {
			boost::hash_combine(res, it.first);
			boost::hash_combine(res, it.second);
		}
		return res;
	}
	
	/// Compose commandline for this tool and the given input file.
	virtual std::string getCommandline(const std::string& file) const {
		return mBinary.native() + " " + mArguments + " " + file;
	}
	/// Compose commandline for this tool with another binary name and the given input file.
	virtual std::string getCommandline(const std::string& file, const std::string& localBinary) const {
		return localBinary + " " + mArguments + " " + file;
	}

	/// Checks whether this cool can handle this file type.
	virtual bool canHandle(const fs::path&) const {
		return true;
	}
	
	/// Compare two tools.
	friend bool operator<(const Tool& lhs, const Tool& rhs) {
		return lhs.mBinary < rhs.mBinary;
	}
	
	/// Recover additional results from the tool output.
	virtual void additionalResults(const fs::path&, BenchmarkResult&) const {}
};

inline std::ostream& operator<<(std::ostream& os, const Tool& tool) {
	return os << tool.binary().native();
}

}
