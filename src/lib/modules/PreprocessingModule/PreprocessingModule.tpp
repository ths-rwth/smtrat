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
		removeFactorsFunction = std::bind(&PreprocessingModule<Settings>::removeFactors, this, std::placeholders::_1);
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
		if (collectBounds) {
			if (addBounds(_subformula->formula())) newBounds.insert(_subformula->formula());
		}
        return true;
    }

    /**
     * Checks the so far received constraints for consistency.
     */
	template<typename Settings>
    Answer PreprocessingModule<Settings>::isConsistent()
    {
		if (collectBounds) {
			// If bounds are collected, check if they are conflicting.
			if (varbounds.isConflicting()) {
				mInfeasibleSubsets.push_back(varbounds.getConflict());
				return foundAnswer(False);
			}
		}
        auto receivedFormula = firstUncheckedReceivedSubformula();
		
        while( receivedFormula != rReceivedFormula().end() )
        {
			FormulaT formula = receivedFormula->formula();
			
			if (collectBounds) {
				// If bounds are collected, check if next subformula is a bound.
				// If so, pass on unchanged.
				auto boundIt = newBounds.find(formula);
				if (boundIt != newBounds.end()) {
					newBounds.erase(boundIt);
					addSubformulaToPassedFormula(formula, receivedFormula->formula());
					++receivedFormula;
					continue;
				}
			}
			
			tmpOrigins.clear();
			tmpOrigins.insert(receivedFormula->formula());
			if (Settings::removeFactors) {
				// Remove redundant or obsolete factors of polynomials.
				formula = visitor.visit(formula, removeFactorsFunction);
			}
			if (Settings::checkBounds) {
				// Check if bounds make constraints vanish.
				formula = visitor.visit(formula, checkBoundsFunction);
			}
			
			SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Received " << receivedFormula->formula());
			SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Result   " << formula);
			
			formula = formula.toCNF();
			FormulaT origins(carl::FormulaType::AND, tmpOrigins);
			
			if (formula.getType() == carl::FormulaType::AND) {
				// If formula has multiple clauses, add separately.
				for (const auto& f: formula.subformulas()) {
					addSubformulaToPassedFormula(f, origins);
				}
			} else {
				addSubformulaToPassedFormula(formula, origins);
			}
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
		if (collectBounds) {
			removeBounds(_subformula->formula());
		}
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
    FormulaT PreprocessingModule<Settings>::removeFactors(FormulaT formula) {
		if(formula.getType() == carl::CONSTRAINT) {
			auto factors = formula.constraint().factorization();
			for (auto it = factors.begin(); it != factors.end();) {
				auto i = carl::IntervalEvaluation::evaluate(it->first, varbounds.getEvalIntervalMap());
				if (i.isPositive()) {
					it = factors.erase(it);
				} else if (i.isSemiPositive()) {
					it->second = 1;
					++it;
				} else if (i.isNegative()) {
					if (it->second % 2 == 0) it = factors.erase(it);
					else {
						it->second = 1;
						++it;
					}
				} else if (i.isSemiNegative()) {
					if (it->second % 2 == 0) it->second = 2;
					else it->second = 1;
					++it;
				} else if (i.isZero()) {
					return FormulaT(newConstraint(Poly(0), formula.constraint().relation()));
				}
			}
			Poly p(1);
			for (const auto& it: factors) {
				p *= carl::pow(it.first, it.second);
			}
			return FormulaT(newConstraint(p, formula.constraint().relation()));
		}
		return formula;
	}
	
	template<typename Settings>
    FormulaT PreprocessingModule<Settings>::checkBounds(FormulaT formula) {
		if(formula.getType() == carl::CONSTRAINT) {
			unsigned result = formula.constraint().evaluate(varbounds.getEvalIntervalMap());
			if (result == 0) {
				accumulateBoundOrigins(formula.constraint());
				return FormulaT(carl::FormulaType::FALSE);
			}
			if (result == 4) {
				accumulateBoundOrigins(formula.constraint());
				return FormulaT(carl::FormulaType::TRUE);
			}
			/*if (result == 1 || result == 2) {
				if (carl::isZero(formula.constraint().constantPart())) {
					if (formula.constraint().lhs().nrTerms() <= 1) return formula;
					FormulasT monomials;
					carl::Sign sign = carl::sgn(formula.constraint().lhs().lcoeff());
					for (TermT t: formula.constraint().lhs()) {
						auto i = carl::IntervalEvaluation::evaluate(t, varbounds.getEvalIntervalMap());
						if (sign != carl::sgn(i)) return formula;
						monomials.emplace(newConstraint(Poly(t.monomial()), carl::Relation::EQ));
					}
					accumulateOrigins(formula.constraint());
					if (result == 1) {
						return FormulaT(carl::FormulaType::AND, monomials);
					} else if (result == 2) {
						return FormulaT(carl::FormulaType::NOT, FormulaT(carl::FormulaType::AND, monomials));
					}
				}
			}*/
		}
		return formula;
	}
}


