#include "NewGBPPModule.h"

#include <carl-arith/poly/umvpoly/functions/Complexity.h>
#include <carl-arith/poly/umvpoly/functions/Groebner.h>
#include <boost/container/flat_set.hpp>

namespace smtrat {

FormulaT replace_groebner(const FormulaT& f) {
	SMTRAT_LOG_FUNC("smtrat.newgbpp", f);

	if (!f.is_nary()) return f;

	FormulasT result;

	if (f.type() == carl::FormulaType::AND) {
		boost::container::flat_set<Poly> equalities;
		std::size_t old_complexity = 0;
		for (const auto& sf : f) {
			if (sf.type() == carl::FormulaType::CONSTRAINT && sf.constraint().relation() == carl::Relation::EQ) {
				equalities.insert(sf.constraint().lhs().normalize());
				old_complexity += carl::complexity(sf.constraint().lhs());
			}
		}
		if (equalities.size()>1) {
			auto basis = carl::groebner_basis(std::vector<Poly>(equalities.begin(), equalities.end()));
			std::size_t new_complexity = 0;
			for (const auto& eq : basis) {
				new_complexity += carl::complexity(eq);
			}
			if (new_complexity <= old_complexity) {
				for (const auto& eq : basis) {
					result.emplace_back(ConstraintT(eq, carl::Relation::EQ));
				}
			}
		} 
		
		if (result.empty()) {
			for (const auto& sf : f) {
				if (sf.type() == carl::FormulaType::CONSTRAINT && sf.constraint().relation() == carl::Relation::EQ) {
					result.emplace_back(sf);
				}
			}
		}
	}

	for (const auto& sf : f) {
		if (sf.is_nary()) {
			result.emplace_back(replace_groebner(sf));
		} else if (sf.type() != carl::FormulaType::CONSTRAINT || sf.constraint().relation() != carl::Relation::EQ || f.type() != carl::FormulaType::AND) {
			result.emplace_back(sf);
		}
	}

	return FormulaT(f.type(), std::move(result));
}

template<class Settings>
NewGBPPModule<Settings>::NewGBPPModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager)
	: PModule(_formula, _conditionals, _manager, Settings::moduleName) {
}

template<class Settings>
NewGBPPModule<Settings>::~NewGBPPModule() {}

template<class Settings>
Answer NewGBPPModule<Settings>::checkCore() {
	FormulaT formula = replace_groebner((FormulaT)rReceivedFormula());
	Answer ans = SAT;
	if (formula.is_false()) {
		ans = UNSAT;
	} else {
		addSubformulaToPassedFormula(formula);
		ans = runBackends();
	}
	if (ans == UNSAT) {
		generateTrivialInfeasibleSubset();
	}
	return ans;
}

} // namespace smtrat
