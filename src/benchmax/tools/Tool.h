#pragma once

#include <filesystem>
#include <functional>
#include <string>
#include <stdexcept>
#include <vector>
#include <regex>

#include <boost/functional/hash.hpp>
#include <boost/version.hpp>

#include <benchmax/benchmarks/BenchmarkSet.h>
#include <benchmax/results/BenchmarkResult.h>
#include <benchmax/settings/Settings.h>
#include <benchmax/utils/filesystem.h>
#include <benchmax/utils/execute.h>


namespace benchmax {

namespace fs = std::filesystem;

inline bool is_system_lib(std::string path) {
	return path.rfind("/usr", 0) == 0 || path.rfind("/lib", 0) == 0;
}

/**
 * Base class for any tool.
 * A tool represents some executable that can be run with some input file.
 * A tool is responsible for
 * - deciding it is applicable for a given file extension,
 * - building a command line to execute it and
 * - parse additional results from stdout / stderr after it has run.
 * 
 * A tool is not to be copied or moved around but should only exist a single time.
 */
class Tool {
protected:
	/// (Non-unique) identifier for the tool.
	std::string mName;
	/// Path to the binary.
	fs::path mBinary;
	/// Command line arguments that should be passed to the binary.
	std::string mArguments;
	/// Attributes of the tool obtained by introspection of the binary.
	std::map<std::string,std::string> mAttributes;
public:
	Tool() = delete;
	Tool(const Tool&) = delete;
	Tool(Tool&&) = delete;
	/// Creates a generic tool from a binary and command line arguments.
	Tool(const fs::path& binary, const std::string& arguments): Tool("Generic", binary, arguments) {}
	/// Creates a named tool from a binary and command line arguments.
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

	/// Get dependencies of binary required to run it (via ldd)
	std::vector<std::string> resolveDependencies() const {
		std::string output;
		std::stringstream ss;
		ss << "ldd " << binary();
		BENCHMAX_LOG_WARN("benchmax.tool", "Determining dependencies using " << ss.str());
		int code = call_program(ss.str(), output);
		if (code == 0) {
			BENCHMAX_LOG_TRACE("benchmax.tool", "Got dependencies");
			std::vector<std::string> results;
			std::regex regex("\\t(.+) => (.+) \\([0-9a-fx]+\\)\\n");
			auto reBegin = std::sregex_iterator(output.begin(), output.end(), regex);
			auto reEnd = std::sregex_iterator();
			for (auto i = reBegin; i != reEnd; ++i) {
				std::string lib = (*i)[1];
				std::string path = (*i)[2];
				if (path == "not found") {
					BENCHMAX_LOG_WARN("benchmax.tool", "Unmet dependency " << lib);
				} else {
					if (!is_system_lib(path)) {
						BENCHMAX_LOG_TRACE("benchmax.tool", "Found dependency " << lib << " (" << path << ")");
						results.emplace_back(path);
					} else {
						BENCHMAX_LOG_TRACE("benchmax.tool", "Skipping system library " << lib << " (" << path << ")");
					}
				}
			}
			return results;
		} else {
			BENCHMAX_LOG_WARN("benchmax.tool", "Could not determine dependencies of binary");
			BENCHMAX_LOG_WARN("benchmax.tool", output);
			return {};
		}
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
	/// Compose commandline for this tool and the given input file.
	virtual std::optional<std::string> parseCommandline(const std::string& cmdline) const {
		std::regex regex(getCommandline("(.+)"));
		std::smatch match;
		if (std::regex_match(cmdline, match, regex)) {
            assert (match.size() == 2);
            return match[1].str();
        } else {
			return {};
		}
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

/// Streaming operator for a generic tool.
inline std::ostream& operator<<(std::ostream& os, const Tool& tool) {
	return os << tool.binary().native();
}

}
