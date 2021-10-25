#pragma once

#include <map>
#include <sstream>
#include <algorithm>
#include <assert.h>

#include "../types.h"

namespace smtrat {
namespace validation {

class ValidationPoint {
private:
	std::string m_channel;
	std::string m_name;
	std::vector<std::pair<FormulaT, bool>> m_formulas;
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
	const auto identifier() const {
		return m_channel + "." + m_name;
	}
	const auto& formulas() const {
		return m_formulas;
	}
	std::size_t add(const FormulaT& f, bool consistent) {
		m_formulas.emplace_back(f, consistent);
		return m_formulas.size() - 1;
	}
	std::size_t add(const FormulasT& fs, bool consistent) {
		m_formulas.emplace_back(FormulaT(carl::FormulaType::AND, fs), consistent);
		return m_formulas.size() - 1;
	}
	std::size_t add(const FormulaSetT& fss, bool consistent) {
		FormulasT fs(fss.begin(), fss.end());
		m_formulas.emplace_back(FormulaT(carl::FormulaType::AND, std::move(fs)), consistent);
		return m_formulas.size() - 1;
	}
	std::size_t add(const ConstraintT& c, bool consistent) {
		m_formulas.emplace_back(FormulaT(c), consistent);
		return m_formulas.size() - 1;
	}
	std::size_t add(const ConstraintsT& cs, bool consistent) {
		FormulasT fs;
		for (const auto& c: cs) {
			fs.emplace_back(c);
		}
		m_formulas.emplace_back(FormulaT(carl::FormulaType::AND, std::move(fs)), consistent);
		return m_formulas.size() - 1;
	}
};

}
}
