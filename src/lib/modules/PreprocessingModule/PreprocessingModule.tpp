/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */


/**
 * @file   PreprocessingModule.cpp
 * @author: Sebastian Junges
 *
 *
 */

#include "PreprocessingModule.h"
#include "../../../cli/ExitCodes.h"
#include <limits.h>
#include <bits/stl_map.h>

//#define REMOVE_LESS_EQUAL_IN_CNF_TRANSFORMATION (Not working)
//#define ADDLINEARDEDUCTIONS
//#define PREPROCESSING_DEVELOP_MODE

namespace smtrat {

	template<typename Settings>
	PreprocessingModule<Settings>::PreprocessingModule( ModuleType _type, const ModuleInput* const _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* const _manager ):
        Module( _type, _formula, _conditionals, _manager )
    {
		checkBoundsFunction = std::bind(&PreprocessingModule<Settings>::checkBounds, this, std::placeholders::_1);
    }

    /**
     * Destructor:
     */
	template<typename Settings>
    PreprocessingModule<Settings>::~PreprocessingModule(){}

    /**
     * Methods:
     */

    /**
     * Adds a constraint to this module.
     *
     * @param _constraint The constraint to add to the already added constraints.
     *
     * @return true
     */
	template<typename Settings>
    bool PreprocessingModule<Settings>::assertSubformula(ModuleInput::const_iterator _subformula) {
        Module::assertSubformula(_subformula);
		if (addBounds(_subformula->formula())) newBounds.insert(_subformula->formula());
        return true;
    }

    /**
     * Checks the so far received constraints for consistency.
     */
	template<typename Settings>
    Answer PreprocessingModule<Settings>::isConsistent()
    {
        auto receivedFormula = firstUncheckedReceivedSubformula();
		
        while( receivedFormula != rReceivedFormula().end() )
        {
			FormulaT formula = receivedFormula->formula();
			
			auto boundIt = newBounds.find(formula);
			if (boundIt != newBounds.end()) {
				newBounds.erase(boundIt);
				addSubformulaToPassedFormula(formula, receivedFormula->formula());
				++receivedFormula;
				continue;
			}
			
			formula = visitor.visit(formula, checkBoundsFunction);
			
			// Inequations are transformed.
			std::cout << "Preprocessing: " << receivedFormula->formula() << std::endl;
			std::cout << "\t -> " << formula << std::endl;
			addSubformulaToPassedFormula(formula, receivedFormula->formula());
			++receivedFormula;
        }

        Answer ans = runBackends();
        if (ans == False) {
            getInfeasibleSubsets();
        }
        return foundAnswer(ans);
    }

    /**
     * Removes a everything related to a sub formula of the received formula.
     *
     * @param _subformula The sub formula of the received formula to remove.
     */
	template<typename Settings>
    void PreprocessingModule<Settings>::removeSubformula(ModuleInput::const_iterator _subformula) {
		removeBounds(_subformula->formula());
        Module::removeSubformula(_subformula);
    }
	
	template<typename Settings>
	void PreprocessingModule<Settings>::updateModel() const {
        clearModel();
        if (solverState() == True) {
            getBackendsModel();
        }
		carl::Variables vars;
		rReceivedFormula().arithmeticVars(vars);
		for (const auto& it: model()) {
			if (!it.first.isVariable()) continue;
			carl::Variable v = it.first.asVariable();
			vars.erase(v);
		}
		for (carl::Variable::Arg v: vars) {
			std::cout << "Setting " << v << " = 0" << std::endl;
			mModel.emplace(v, vs::SqrtEx());
		}
		std::cout << mModel << std::endl;
    }
	
	template<typename Settings>
    bool PreprocessingModule<Settings>::addBounds(FormulaT formula) {
		switch (formula.getType()) {
			case carl::CONSTRAINT:
				return varbounds.addBound(formula.pConstraint(), formula);
			case carl::AND: {
				bool found = false;
				for (const auto& f: formula.subformulas()) found |= addBounds(f);
				return found;
			}
			default: break;
		}
		return false;
	}
	template<typename Settings>
    void PreprocessingModule<Settings>::removeBounds(FormulaT formula) {
		switch (formula.getType()) {
			case carl::CONSTRAINT:
				varbounds.removeBound(formula.pConstraint(), formula);
				break;
			case carl::AND:
				for (const auto& f: formula.subformulas()) removeBounds(f);
				break;
			default: break;
		}
	}
	
	template<typename Settings>
    FormulaT PreprocessingModule<Settings>::checkBounds(FormulaT formula) {
		if(formula.getType() == carl::CONSTRAINT) {
			unsigned result = formula.constraint().evaluate(varbounds.getEvalIntervalMap());
			if (result == 0) return FormulaT(carl::FormulaType::FALSE);
			if (result == 2) return FormulaT(carl::FormulaType::TRUE);
		}
		return formula;
	}
}


