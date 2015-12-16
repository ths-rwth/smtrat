/**
 * @file MCB.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-12-10
 * Created on 2015-12-10.
 */

#include "MCBModule.h"
#include "../../datastructures/model/Model.h"

namespace smtrat
{
	class MCBModelSubstitution: public ModelSubstitution {
	private:
		std::map<carl::Variable,Rational> mAssignments;
	public:
		MCBModelSubstitution(const std::map<carl::Variable,Rational>& assignments): ModelSubstitution(), mAssignments(assignments) {}
		virtual ModelValue evaluate(Model& model) {
			auto selection = mAssignments.end();
			for (auto it = mAssignments.begin(); it != mAssignments.end(); it++) {
				auto mit = model.find(ModelVariable(it->first));
				assert(mit != model.end());
				assert(mit->second.isBool());
				if (mit->second.asBool()) {
					assert(selection == mAssignments.end());
					selection = it;
				}
			}
			return ModelValue(selection->second);
		}
		virtual bool dependsOn(const ModelVariable& var) const {
			if (!var.isVariable()) return false;
			return mAssignments.find(var.asVariable()) != mAssignments.end();
		}
		virtual void print(std::ostream& os) const {
			os << "[";
			for (auto it = mAssignments.begin(); it != mAssignments.end(); it++) {
				if (it != mAssignments.begin()) os << ", ";
				os << it->first << " -> " << it->second;
			}
			os << "]";
		}
	};
	
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
		if (solverState() != UNSAT) {
			getBackendsModel();
			for (const auto& choice: mChoices) {
				if (mRemaining.count(choice.first) > 0) continue;
				ModelVariable var(choice.first);
				std::map<BVar,Rational> assignment;
				for (const auto& v: choice.second) {
					assignment.emplace(v.second.first, v.first);
				}
				mModel.emplace(var, ModelSubstitution::create<MCBModelSubstitution>(assignment));
			}
		}
	}
	
	template<class Settings>
	Answer MCBModule<Settings>::checkCore( bool _full, bool _minimize )
	{
		mRemaining.clear();
		mChoices.clear();
		carl::FormulaVisitor<FormulaT> visitor;
		auto receivedFormula = firstUncheckedReceivedSubformula();
		while (receivedFormula != rReceivedFormula().end()) {
			visitor.visit(receivedFormula->formula(), collectChoicesFunction);
			receivedFormula++;
		}
		FormulaT newFormula = applyReplacements(FormulaT(rReceivedFormula()));
		clearPassedFormula();
		addSubformulaToPassedFormula(newFormula);
		
		Answer ans = runBackends(_full, _minimize);
		if (ans == UNSAT) {
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
			AVar var = poly.first.getSingleVariable();
			std::vector<std::pair<Rational,FormulaT>> choices;
			for (const auto& entry: poly.second) {
				if (entry.second.first != carl::Relation::EQ) break;
				choices.emplace_back(entry.first, entry.second.second);
			}
			if (choices.size() != poly.second.size()) continue;
			auto& m = mChoices[var];
			for (const auto& c: choices) {
				auto it = m.find(c.first);
				if (it == m.end()) {
					m.emplace(c.first, std::make_pair(carl::freshBooleanVariable(), c.second));
				}
			}
		}
	}
	
	template<typename Settings>
	FormulaT MCBModule<Settings>::applyReplacements(const FormulaT& f) {
		std::set<AVar> variables;
		std::map<FormulaT, FormulaT> repl;
		for (const auto& r: mChoices) {
			variables.insert(r.first);
			for (const auto& f: r.second) {
				BVar v = f.second.first;
				const FormulaT& form = f.second.second;
				repl.emplace(form, FormulaT(v));
			}
		}
		carl::FormulaSubstitutor<FormulaT> subs;
		FormulaT res = subs.substitute(f, repl);
		
		mRemaining.clear();
		res.allVars(mRemaining);
		FormulasT impl;
		for (const auto& v: variables) {
			if (mRemaining.count(v) > 0) {
				for (const auto& r: mChoices.at(v)) {
					impl.push_back(FormulaT(carl::FormulaType::IMPLIES, {FormulaT(r.second.first), r.second.second}));
				}
			}
		}
		if (impl.empty()) return res;
		impl.push_back(res);
		return FormulaT(carl::FormulaType::AND, std::move(impl));
	}
}

#include "Instantiation.h"
