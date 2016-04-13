/**
 * File:   Tool.h
 * @author Sebastian Junges
 * @author Ulrich Loup
 *
 * @since 2012-09-25
 * @version 2013-03-19
 */

#pragma once

#include <functional>
#include <string>
#include <stdexcept>
#include <vector>

#ifdef __VS
#pragma warning(push, 0)
#include <boost/functional/hash.hpp>
#include <boost/version.hpp>
#include <boost/filesystem.hpp>
#pragma warning(pop)
#else
#include <boost/functional/hash.hpp>
#include <boost/version.hpp>
#include <boost/filesystem.hpp>
#endif

#include "../BenchmarkStatus.h"

namespace benchmax {

namespace fs = boost:: filesystem;

class Tool {
protected:
	std::string mName;
	fs::path mBinary;
	std::string mArguments;
	std::map<std::string,std::string> mAttributes;
public:
	Tool(const fs::path& binary, const std::string& arguments): Tool("Generic", binary, arguments) {}
	Tool(const std::string& name, const fs::path& binary, const std::string& arguments): mName(name), mBinary(binary), mArguments(arguments) {}
	Tool(const Tool&) = delete;
	virtual ~Tool() {}

	std::string name() const {
		return mName;
	}
	
	fs::path binary() const {
		return mBinary;
	}
	
	const std::map<std::string,std::string>& attributes() const {
		return mAttributes;
	}
	
	std::size_t attributeHash() const {
		std::size_t res = 0;
		for (const auto& it: mAttributes) {
			boost::hash_combine(res, it.first);
			boost::hash_combine(res, it.second);
		}
		return res;
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
		if (!fs::is_regular_file(path)) return false;
		return fs::extension(path) == extension;
	}
	virtual bool canHandle(const fs::path&) const {
		return true;
	}
	
	virtual std::string getStatus(const BenchmarkResult&) const {
		return "";
	}
	
	friend bool operator<(const Tool& lhs, const Tool& rhs) {
		return lhs.mBinary < rhs.mBinary;
	}
	
	virtual void additionalResults(const fs::path&, BenchmarkResult&) const {}
};

inline std::ostream& operator<<(std::ostream& os, const Tool& tool) {
	return os << tool.binary().native();
}

}
