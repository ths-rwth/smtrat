#pragma once

#include <map>
#include <sstream>
#include <algorithm>
#include <assert.h>

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
	std::string m_name;
	#ifndef VALIDATION_STORE_STRINGS
	std::vector<std::pair<FormulaT, bool>> m_formulas;
	#else
	std::vector<std::pair<std::string, bool>> m_formulas;
	#endif
public:
	void set_identifier(const std::string& channel, const std::string& name) {
		m_channel = channel;
		m_name = name;
	}
	const auto& channel() const {
		return m_channel;
	}
	const auto& name() const {
		return m_name;
	}
	auto identifier() const {
		return m_channel + "." + m_name;
	}
	const auto& formulas() const {
		return m_formulas;
	}
	std::size_t add(const FormulaT& f, bool consistent) {
		#ifndef VALIDATION_STORE_STRINGS
		m_formulas.emplace_back(f, consistent);
		#else
		carl::SMTLIBStream sls;
		sls.declare(f.logic());
		sls.declare(carl::variables(f));
		sls.assertFormula(f);
		m_formulas.emplace_back(sls.str(), consistent);
		#endif
		return m_formulas.size() - 1;
	}
	std::size_t add(const FormulasT& fs, bool consistent) {
		return add(FormulaT(carl::FormulaType::AND, fs), consistent);
	}
	std::size_t add(const FormulaSetT& fss, bool consistent) {
		FormulasT fs(fss.begin(), fss.end());
		return add(FormulaT(carl::FormulaType::AND, std::move(fs)), consistent);
	}
	std::size_t add(const ConstraintT& c, bool consistent) {
		return add(FormulaT(c), consistent);
	}
	std::size_t add(const ConstraintsT& cs, bool consistent) {
		FormulasT fs;
		for (const auto& c: cs) {
			fs.emplace_back(c);
		}
		return add(FormulaT(carl::FormulaType::AND, std::move(fs)), consistent);
	}
};

}
}
