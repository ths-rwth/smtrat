#include "PNFerModule.h"

#include <carl-formula/formula/functions/PNF.h>

namespace smtrat {
PNFerModule::PNFerModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* const _manager)
	: PModule(_formula, _conditionals, _manager) {
}

PNFerModule::~PNFerModule() {}

Answer PNFerModule::checkCore() {
	FormulaT input(rReceivedFormula());
	FormulaT pnf;
	if ((carl::PROP_CONTAINS_QUANTIFIER_EXISTS <= input.properties()) || (carl::PROP_CONTAINS_QUANTIFIER_FORALL <= input.properties())) {
		auto [prefix, matrix] = carl::to_pnf(input);
		auto contains_forall = std::find_if(prefix.begin(), prefix.end(), [](const auto& e) { return e.first == carl::Quantifier::FORALL; }) != prefix.end();
		if (contains_forall) {
			pnf = carl::to_formula(prefix, matrix);
		} else {
			pnf = input;
		}
	} else {
		pnf = input;
	}

	if (pnf.type() == carl::FormulaType::FALSE) {
		generateTrivialInfeasibleSubset();
		return UNSAT;
	} else {
		addSubformulaToPassedFormula(pnf, input);
	}

	if (rPassedFormula().empty() && solverState() == UNKNOWN) {
		return SAT;
	} else {
		Answer a = runBackends();
		if (a == UNSAT) {
			getInfeasibleSubsets();
		}
		return a;
	}
}
} // namespace smtrat
