#pragma once

#include "Tool.h"

#include <regex>
#include <initializer_list>

namespace benchmax {

class simple_parser {
	std::string::const_iterator m_iter;
	const std::string::const_iterator m_end;

public:
	simple_parser(const std::string& content) : m_iter(content.cbegin()), m_end(content.cend()) {}
	bool expect(const char c) {
		bool result = m_iter != m_end && *m_iter == c;
		if (result) m_iter++;
		return result;
	}
	bool expect_end() {
		return m_iter == m_end;
	}
	void skip_whitespace() {
		while (m_iter != m_end && isspace(*m_iter)) m_iter++;
	}
	void skip_excluding(const char c) {
		if (m_iter == m_end || *m_iter == c) return;
		do m_iter++; while (m_iter != m_end && *m_iter != c);
	}
	std::optional<std::string> read_until(const char c) {
		std::stringstream ss;
		while (m_iter != m_end && *m_iter != c) {
			ss << *m_iter;
			m_iter++;
		}
		if  (m_iter == m_end) return std::nullopt;
		else return ss.str();
	}
	std::optional<std::string> read_until_whitespace() {
		std::stringstream ss;
		while (m_iter != m_end && !isspace(*m_iter)) {
			ss << *m_iter;
			m_iter++;
		}
		if  (m_iter == m_end) return std::nullopt;
		else return ss.str();
	}
	std::optional<std::string> read_until_whitespace_or(const std::initializer_list<char> cs) {
		std::stringstream ss;
		while (m_iter != m_end && !isspace(*m_iter) && std::find(cs.begin(), cs.end(), *m_iter) == cs.end()) {
			ss << *m_iter;
			m_iter++;
		}
		if  (m_iter == m_end) return std::nullopt;
		else return ss.str();
	}
};

/**
 * Tool wrapper for SMT-RAT for SMT-LIB.
 */
class SMTRAT: public Tool {
public:
	/// New SMT-RAT tool.
	SMTRAT(const fs::path& binary, const std::string& arguments): Tool("SMTRAT", binary, arguments) {
		if (settings_tools().collect_statistics) mArguments += " --stats.print";
	}

	/// Only handle .smt2 files.
	virtual bool canHandle(const fs::path& path) const override {
		return is_extension(path, ".smt2");
	}
	
	/// Try to parse memouts from stderr.
	std::string getStatusFromOutput(const BenchmarkResult& result) const {
		if (result.stderr.find("GNU MP: Cannot allocate memory") != std::string::npos) return "memout";
		if (result.stderr.find("Minisat::OutOfMemoryException") != std::string::npos) return "memout";
		return "segfault";
	}

	bool parse_stats(BenchmarkResult& result) const {
		auto first_colon = result.stdout.find(':');
		if (first_colon == std::string::npos) return false;
		assert(first_colon>0);
		first_colon--;
		auto str = result.stdout.substr(first_colon);
		simple_parser p(str);
		p.skip_excluding('(');
		while (p.expect('(')) {
			if (!p.expect(':')) return false;
			auto prefix = p.read_until_whitespace();
			if (!prefix) return false;
			p.skip_whitespace();
			if (!p.expect('(')) return false;
			p.skip_whitespace();
			while (p.expect(':')) {
				auto key = p.read_until_whitespace();
				if (!key) return false;
				p.skip_whitespace();
				auto value = p.read_until_whitespace_or({')', ':'});
				if (!value) return false;
				result.additional.emplace(*prefix + "_" + *key, *value);
				p.skip_whitespace();
			}
			if (!p.expect(')')) return false;
			p.skip_whitespace();
			if (!p.expect(')')) return false;
			p.skip_whitespace();
		}
		return true;
	}
	
	/// Computes the answer string from the exit code and parses statistics output.
	virtual void additionalResults(const fs::path&, BenchmarkResult& result) const override {
		switch (result.exitCode) {
			case 2: result.answer = "sat"; break;
			case 3: result.answer = "unsat"; break;
			case 4: result.answer = "unknown"; break;
			case 5: result.answer = "wrong"; break;
			case 9: result.answer = "nosuchfile"; break;
			case 10: result.answer = "parsererror"; break;
			case 11: result.answer = "timeout"; break;
			case 12: result.answer = "memout"; break;
			default: result.answer = getStatusFromOutput(result);
		}

		if (true) {
			if (settings_tools().collect_statistics && !parse_stats(result)) {
				BENCHMAX_LOG_WARN("benchmax.tool.SMTRAT", "Error while parsing statistics of result: " << result);
			}
		} else {
			std::regex topRegex("\\(\\:(\\S+)\\s*\\(\\s*((?:\\:\\S+\\s*\\S+\\s*)+)\\)\\)");
			std::regex subRegex("\\s*\\:(\\S+)\\s*(\\S+)");

			auto topBegin = std::sregex_iterator(result.stdout.begin(), result.stdout.end(), topRegex);
			auto topEnd = std::sregex_iterator();
			for (auto i = topBegin; i != topEnd; ++i) {
				const std::string& prefix = (*i)[1];
				const std::string& subStdout = (*i)[2];

				auto subBegin = std::sregex_iterator(subStdout.begin(), subStdout.end(), subRegex);
				auto subEnd = std::sregex_iterator();
				for (auto j = subBegin; j != subEnd; ++j) {
					std::string name = prefix + "_" + std::string((*j)[1]);
					result.additional.emplace(name, (*j)[2]);
				}
			}
		}
	}
};

}
