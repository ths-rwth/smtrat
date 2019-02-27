/**
 * @file Symmetry.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2018-03-12
 * Created on 2018-03-12.
 */

#include "SymmetryModule.h"

#include <carl/formula/symmetry/symmetry.h>

namespace smtrat
{
	template<class Settings>
	SymmetryModule<Settings>::SymmetryModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
		PModule( _formula, _conditionals, _manager, Settings::moduleName )
	{}
	
	template<class Settings>
	SymmetryModule<Settings>::~SymmetryModule()
	{}
	
	template<class Settings>
	Answer SymmetryModule<Settings>::checkCore()
	{
		for (auto it = rReceivedFormula().begin(); it != rReceivedFormula().end(); ++it) {
			addReceivedSubformulaToPassedFormula(it);
		}
		auto symm = carl::formula::breakSymmetries(FormulaT(rPassedFormula()));
		if (!symm.isTrue()) {
			SMTRAT_LOG_DEBUG("smtrat.symmetry", "Broke symmetries by" << std::endl << symm);
			addSubformulaToPassedFormula(symm);
		}
		
		Answer ans = runBackends();
		if (ans == UNSAT) {
			generateTrivialInfeasibleSubset();
		}
		return ans;
	}
}

#include "Instantiation.h"
