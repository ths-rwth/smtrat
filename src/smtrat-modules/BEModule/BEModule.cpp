/**
 * @file BEModule.tpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-09-09
 * Created on 2015-09-09.
 */

#include "BEModule.h"

namespace smtrat
{
    template<class Settings>
    BEModule<Settings>::BEModule( const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager ):
        PModule( _formula, _conditionals, _manager ),
        mVisitor()
    {
        extractBoundsFunction = std::bind(&BEModule<Settings>::extractBounds, this, std::placeholders::_1);
    }

    template<class Settings>
    BEModule<Settings>::~BEModule()
    {}

    template<class Settings>
    Answer BEModule<Settings>::checkCore()
    {
        auto receivedFormula = firstUncheckedReceivedSubformula();
        while( receivedFormula != rReceivedFormula().end() )
        {
            FormulaT formula = mVisitor.visitResult( receivedFormula->formula(), extractBoundsFunction );
            if( formula.isFalse() )
            {
                receivedFormulasAsInfeasibleSubset( receivedFormula );
                return UNSAT;
            }
            if( !formula.isTrue() )
                addSubformulaToPassedFormula( formula, receivedFormula->formula() );
            ++receivedFormula;
        }
        Answer ans = runBackends();
        if( ans == UNSAT )
            generateTrivialInfeasibleSubset(); // TODO: compute a better infeasible subset
        return ans;
    }
	
    template<typename Settings>
    FormulaT BEModule<Settings>::extractBounds(const FormulaT& formula)
    {
		if (formula.getType() != carl::FormulaType::OR && formula.getType() != carl::FormulaType::AND) return formula;
		bool conjunction = formula.getType() == carl::FormulaType::AND;
	
		FormulaT::ConstraintBounds cb;
		collectBounds(cb, formula, conjunction);
		if (cb.empty()) return formula;
		//std::cout << cb << std::endl;
			
		if (conjunction) {
			FormulasT f;
			FormulaT::swapConstraintBounds(cb, f, conjunction);
			f.push_back(formula);
			return FormulaT(carl::FormulaType::AND, std::move(f));
		} else {
			for (const auto& poly: cb) {
				if (!poly.first.isVariable()) continue;
				std::vector<Choice> choices;
				for (const auto& entry: poly.second) {
					if (entry.second.first != carl::Relation::EQ) break;
					choices.emplace_back(poly.first.getSingleVariable(), entry.second.second);
				}
				if (choices.size() != poly.second.size()) continue;
				for (const auto& c: choices) {
					auto it = mReplacements.find(c);
					if (it == mReplacements.end()) {
						mReplacements.emplace(c, carl::freshBooleanVariable());
					}
				}
			}
		}
		return formula;
	}
	
	template<typename Settings>
	void BEModule<Settings>::collectBounds(FormulaT::ConstraintBounds& cb, const FormulaT& formula, bool conjunction) const {
		for (const auto& f: formula.subformulas()) {
			if (f.getType() == carl::FormulaType::CONSTRAINT || (f.getType() == carl::FormulaType::NOT && f.subformula().getType() == carl::FormulaType::CONSTRAINT)) {
				FormulaT::addConstraintBound(cb, f, conjunction);
			}
		}
	}
	
	template<typename Settings>
	FormulaT BEModule<Settings>::applyReplacements(const FormulaT& f) const {
		std::vector<carl::Variable> variables;
		std::map<FormulaT, FormulaT> repl;
		for (const auto& r: mReplacements) {
			carl::Variable v = std::get<0>(r.first);
			FormulaT form = std::get<1>(r.first);
			std::cout << "Handling " << form << std::endl;
			
			variables.push_back(v);
			repl.emplace(form, FormulaT(r.second));
		}
		carl::FormulaSubstitutor<FormulaT> subs;
		std::cout << "Doing substitution..." << std::endl;
		FormulaT res = subs.substitute(f, repl);
		std::cout << "Done." << std::endl;
		carl::Variables remainingVars;
		res.allVars(remainingVars);
		FormulasT impl;
		for (const auto& v: variables) {
			if (remainingVars.count(v) > 0) {
				std::cout << "Checking for " << v << std::endl;
				for (const auto& r: mReplacements) {
					if (v != std::get<0>(r.first)) continue;
					FormulaT form = std::get<1>(r.first);
					impl.push_back(FormulaT(carl::FormulaType::IMPLIES, {FormulaT(r.second), form}));
				}
			}
		}
		if (impl.empty()) return res;
		impl.push_back(res);
		return FormulaT(carl::FormulaType::AND, std::move(impl));
	}
}

#include "Instantiation.h"
