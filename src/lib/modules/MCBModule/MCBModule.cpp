/**
 * @file MCB.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-12-10
 * Created on 2015-12-10.
 */

#include "MCBModule.h"

namespace smtrat
{
	template<class Settings>
	MCBModule<Settings>::MCBModule(const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager):
		PModule( _formula, _conditionals, _manager )
#ifdef SMTRAT_DEVOPTION_Statistics
		, mStatistics(Settings::moduleName)
#endif
	{
        collectChoicesFunction = std::bind(&MCBModule<Settings>::collectChoices, this, std::placeholders::_1);
	}
	
	template<class Settings>
	MCBModule<Settings>::~MCBModule()
	{}
	
	template<class Settings>
	void MCBModule<Settings>::updateModel() const
	{
		mModel.clear();
		if( solverState() == True )
		{
			getBackendsModel();
			for (const auto& choice: mChoices) {
				ModelVariable var(choice.second);
				auto val = mModel.find(var);
				assert(val != mModel.end());
				assert(val->second.isBool());
				if (val->second.asBool()) {
					ModelVariable arithvar(std::get<0>(choice.first));
					auto arithval = mModel.find(arithvar);
					if (arithval == mModel.end()) {
						mModel.emplace(arithvar, ModelValue(std::get<1>(choice.first)));
					}
				}
				mModel.erase(var);
			}
		}
	}
	
	template<class Settings>
	Answer MCBModule<Settings>::checkCore( bool _full, bool _minimize )
	{
		carl::FormulaVisitor<FormulaT> visitor;
        auto receivedFormula = firstUncheckedReceivedSubformula();
        while (receivedFormula != rReceivedFormula().end()) {
            visitor.visitVoid(receivedFormula->formula(), collectChoicesFunction);
			receivedFormula++;
        }
		for (const auto& r: mChoices) {
			std::cout << r.first << " -> " << r.second << std::endl;
		}
		FormulaT newFormula = applyReplacements(FormulaT(rReceivedFormula()));
		clearPassedFormula();
		addSubformulaToPassedFormula(newFormula);
		
		Answer ans = runBackends(_full, _minimize);
        if (ans == False) {
            generateTrivialInfeasibleSubset();
		}
        return ans;
	}
	
	template<typename Settings>
	void MCBModule<Settings>::collectBounds(FormulaT::ConstraintBounds& cb, const FormulaT& formula, bool conjunction) const {
		for (const auto& f: formula.subformulas()) {
			if (f.getType() == carl::FormulaType::CONSTRAINT || (f.getType() == carl::FormulaType::NOT && f.subformula().getType() == carl::FormulaType::CONSTRAINT)) {
				FormulaT::addConstraintBound(cb, f, conjunction);
			}
		}
	}
	
	template<typename Settings>
	void MCBModule<Settings>::collectChoices(const FormulaT& formula) {
		if (formula.getType() != carl::FormulaType::OR) return;
		
		FormulaT::ConstraintBounds cb;
		collectBounds(cb, formula, false);
		if (cb.empty()) return;
			
		for (const auto& poly: cb) {
			if (!poly.first.isVariable()) continue;
			std::vector<Choice> choices;
			for (const auto& entry: poly.second) {
				if (entry.second.first != carl::Relation::EQ) break;
				choices.emplace_back(poly.first.getSingleVariable(), entry.first, entry.second.second);
			}
			if (choices.size() != poly.second.size()) continue;
			for (const auto& c: choices) {
				auto it = mChoices.find(c);
				if (it == mChoices.end()) {
					mChoices.emplace(c, carl::freshBooleanVariable());
				}
			}
		}
	}
	
	template<typename Settings>
	FormulaT MCBModule<Settings>::applyReplacements(const FormulaT& f) const {
		std::set<carl::Variable> variables;
		std::map<FormulaT, FormulaT> repl;
		for (const auto& r: mChoices) {
			carl::Variable v = std::get<0>(r.first);
			const FormulaT& form = std::get<2>(r.first);
			variables.insert(v);
			repl.emplace(form, FormulaT(r.second));
		}
		carl::FormulaSubstitutor<FormulaT> subs;
		FormulaT res = subs.substitute(f, repl);
		
		carl::Variables remainingVars;
		res.allVars(remainingVars);
		FormulasT impl;
		for (const auto& v: variables) {
			if (remainingVars.count(v) > 0) {
				for (const auto& r: mChoices) {
					if (v != std::get<0>(r.first)) continue;
					FormulaT form = std::get<2>(r.first);
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
