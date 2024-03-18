#pragma once

#include <map>
#include <sstream>
#include <algorithm>
#include <cassert>
#include <tuple>

#include "../types.h"

#define VALIDATION_STORE_STRINGS


#ifdef VALIDATION_STORE_STRINGS
#include <carl-io/SMTLIBStream.h>
#endif

namespace smtrat {
namespace validation {

class ValidationPoint {
private:
	std::string m_channel;
	std::string m_file;
	int m_line;
	#ifndef VALIDATION_STORE_STRINGS
	std::vector<std::tuple<FormulaT, bool, std::string>> m_formulas;
	#else
	std::vector<std::tuple<std::string, bool, std::string>> m_formulas;
	#endif
public:
	void set_identifier(const std::string& channel, const std::string& file, int line) {
		m_channel = channel;
		m_file = file;
		m_line = line;
	}
	const auto& channel() const {
		return m_channel;
	}
	auto identifier() const {
		return m_channel + "  " + m_file + ":" + std::to_string(m_line);
	}
	const auto& formulas() const {
		return m_formulas;
	}
	std::size_t add(const FormulaT& f, bool consistent, const std::string& name) {
		#ifndef VALIDATION_STORE_STRINGS
		m_formulas.emplace_back(f, consistent, name);
		#else
		carl::io::SMTLIBStream sls;
		sls.declare(f.logic());
		sls.declare(carl::variables(f));
		sls.assertFormula(f);
		m_formulas.emplace_back(sls.str(), consistent, name);
		#endif
		return m_formulas.size() - 1;
	}
	std::size_t add(const FormulasT& fs, bool consistent, const std::string& name) {
		return add(FormulaT(carl::FormulaType::AND, fs), consistent, name);
	}
	std::size_t add(const FormulaSetT& fss, bool consistent, const std::string& name) {
		FormulasT fs(fss.begin(), fss.end());
		return add(FormulaT(carl::FormulaType::AND, std::move(fs)), consistent, name);
	}
	std::size_t add(const ConstraintT& c, bool consistent, const std::string& name) {
		return add(FormulaT(c), consistent, name);
	}
	std::size_t add(const ConstraintsT& cs, bool consistent, const std::string& name) {
		FormulasT fs;
		for (const auto& c: cs) {
			fs.emplace_back(c);
		}
		return add(FormulaT(carl::FormulaType::AND, std::move(fs)), consistent, name);
	}
};

}
}
