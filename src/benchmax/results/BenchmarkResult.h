#pragma once

#include <chrono>
#include <iostream>
#include <map>

#include <boost/archive/text_iarchive.hpp>
#include <boost/archive/text_oarchive.hpp>
#include <boost/serialization/map.hpp>
#include <fstream>
#include <filesystem>

#include "../settings/Settings.h"

namespace benchmax {

/**
 * Results for a single benchmark run.
 */
struct BenchmarkResult {
	/// Shell exit code.
	int exitCode;
	/// Runtime in milliseconds.
	std::chrono::milliseconds time;
	/// Answer string.
	std::string answer;
	/// Standard output (mostly for parsing the answer and additional information).
	std::string stdout;
	/// Error output (mostly for parsing the answer and additional information).
	std::string stderr;
	/// Arbitrary additional information that can be provided by the tool class.
	mutable std::map<std::string, std::string> additional;
	/// Identifier for temporary file.
	mutable size_t stored_id = 0;
	
	/**
	 * Properly detect timeouts.
	 * Most backends give processes a bit more time to avoid having race-condition-like situations.
	 */
	template<typename TimeLimit>
	void cleanup(const TimeLimit& limit) {
		if (time > limit) {
			answer = "timeout";
		}
		stdout = "";
		stderr = "";
	}

	auto get_path() const {
		assert(stored_id > 0);
		return std::filesystem::temp_directory_path()/("benchmark-result-" + std::to_string(stored_id) + ".xml");
	}
	void store(size_t id) const {
		if (settings_operation().use_temp) {
			stored_id = id;
			std::ofstream ofs(get_path());
			boost::archive::text_oarchive oa(ofs);
			oa << additional;
			store();
		}
	}
	void store() const {
		if (settings_operation().use_temp) {
			additional.clear();
		}
	}
	void restore() const {
		if (settings_operation().use_temp) {
			std::ifstream ifs(get_path());
			boost::archive::text_iarchive ia(ifs);
			ia >> additional;
		}
	}
	void forget() const {
		if (settings_operation().use_temp) {
			std::filesystem::remove(get_path());
			additional.clear();
		}
	}
};

/// Streaming operator for BenchmarkResult.
inline std::ostream& operator<<(std::ostream& os, const BenchmarkResult& results) {
	os << "(" << results.answer << ", " << results.exitCode << ", " << results.time.count() << "ms)" << std::endl;
	os << results.stdout << std::endl;
	os << results.stderr << std::endl;
	return os;
}


}
