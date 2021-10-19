#pragma once

#include "ValidationCollector.h"

#include <map>
#include <sstream>
#include <algorithm>
#include <assert.h>

namespace smtrat {
namespace validation {

class ValidationPoint {
private:
	std::string mName;
	std::vector<std::pair<FormulaT, bool>> mFormulas;
protected:
	std::size_t add(const FormulaT& f, bool consistent) {
		mFormulas.emplace_back(f, consistent);
		return mFormulas.size() - 1;
	}
	std::size_t add(const FormulasT& fs, bool consistent) {
		mFormulas.emplace_back(FormulaT(carl::FormulaType::AND, fs), consistent);
		return mFormulas.size() - 1;
	}
	std::size_t add(const FormulaSetT& fss, bool consistent) {
		FormulasT fs(fss.begin(), fss.end());
		mFormulas.emplace_back(FormulaT(carl::FormulaType::AND, std::move(fs)), consistent);
		return mFormulas.size() - 1;
	}
	std::size_t add(const ConstraintT& c, bool consistent) {
		mFormulas.emplace_back(FormulaT(c), consistent);
		return mFormulas.size() - 1;
	}
	std::size_t add(const ConstraintsT& cs, bool consistent) {
		FormulasT fs;
		for (const auto& c: cs) {
			fs.emplace_back(cs);
		}
		mFormulas.emplace_back(FormulaT(carl::FormulaType::AND, std::move(fs)), consistent);
		return mFormulas.size() - 1;
	}
public:
	void set_name(const std::string& name) {
		mName = name;
	}
	const auto& name() const {
		return mName;
	}
	const auto& formulas() const {
		return mFormulas;
	}
};

}
}
