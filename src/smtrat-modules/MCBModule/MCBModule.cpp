/**
 * @file MCB.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-12-10
 * Created on 2015-12-10.
 */

#include "MCBModule.h"

#include <smtrat-common/model.h>

namespace smtrat
{
	class MCBModelSubstitution: public ModelSubstitution {
	private:
		std::map<carl::Variable,Rational> mAssignments;
		Rational mDefault;
	public:
		MCBModelSubstitution(const std::map<carl::Variable,Rational>& assignments): ModelSubstitution(), mAssignments(assignments), mDefault(0) {
			for (const auto& a: mAssignments) {
				if (a.second >= mDefault) mDefault = carl::ceil(a.second) + 1;
			}
		}
		virtual void multiplyBy(const Rational& _number) {
			for (auto& a: mAssignments)
				a.second *= _number;
		}
		virtual void add(const Rational& _number) {
			for (auto& a: mAssignments)
				a.second += _number;
		}
		virtual carl::ModelSubstitutionPtr<Rational,Poly> clone() const {
			return carl::createSubstitutionPtr<Rational,Poly,MCBModelSubstitution>(mAssignments);
		}
		virtual FormulaT representingFormula( const ModelVariable& mv ) {
			assert(false);
			return FormulaT();
		}
		virtual ModelValue evaluateSubstitution(const Model& model) const {
			auto selection = mAssignments.end();
			for (auto it = mAssignments.begin(); it != mAssignments.end(); it++) {
				const ModelValue& mv = model.evaluated(ModelVariable(it->first));
				assert(mv.isBool());
				if (mv.asBool()) {
					assert(selection == mAssignments.end());
					selection = it;
					SMTRAT_LOG_DEBUG("smtrat.mcb", "Evaluating " << *this << " to " << selection->second << " on " << model);
					break;
				}
			}
			if (selection == mAssignments.end()) {
				SMTRAT_LOG_DEBUG("smtrat.mcb", "Evaluating " << *this << " to default " << mDefault << " on " << model);
				return ModelValue(mDefault);
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
	MCBModule<Settings>::MCBModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
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
	Answer MCBModule<Settings>::checkCore()
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
		
		Answer ans = runBackends();
		if (ans == UNSAT) {
			generateTrivialInfeasibleSubset();
		}
		return ans;
	}
	
	template<typename Settings>
	void MCBModule<Settings>::updateModel() const {
		clearModel();
		if (solverState() == SAT || (solverState() != UNSAT && appliedPreprocessing())) {
			getBackendsModel();
			mModel.update(mAssignments);
			mAssignments.clear();
		}
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
		if (mChoices.empty()) return f;
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
		SMTRAT_LOG_DEBUG("smtrat.mcb", "Applying " << repl << " on \n\t" << f);
		FormulaT res = subs.substitute(f, repl);
		SMTRAT_LOG_DEBUG("smtrat.mcb", "Resulting in\n\t" << res);
		
		mRemaining.clear();
		res.allVars(mRemaining);
		FormulasT equiv;
		for (const auto& v: variables) {
			if (mRemaining.count(v) > 0) {
				// Variable is still in the formula
				for (const auto& r: mChoices.at(v)) {
					equiv.push_back(FormulaT(carl::FormulaType::IFF, {FormulaT(r.second.first), r.second.second}));
				}
			} else {
				// Variable has been eliminated
				ModelVariable var(v);
				std::map<BVar,Rational> assignment;
				for (const auto& c: mChoices.at(v)) {
					assignment.emplace(c.second.first, c.first);
				}
				SMTRAT_LOG_DEBUG("smtrat.mcb", "Adding " << var << " = " << assignment);
				mAssignments.emplace(var, carl::createSubstitution<Rational,Poly,MCBModelSubstitution>(assignment));
			}
			for (const auto& c1: mChoices.at(v)) {
				for (const auto& c2: mChoices.at(v)) {
					if (c1.second.first >= c2.second.first) continue;
					equiv.push_back(FormulaT(carl::FormulaType::OR, {FormulaT(c1.second.first).negated(), FormulaT(c2.second.first).negated()}));
					SMTRAT_LOG_DEBUG("smtrat.mcb", "Adding exclusion " << equiv.back());
				}
			}
		}
		if (equiv.empty()) return res;
		SMTRAT_LOG_DEBUG("smtrat.mcb", "Adding equivalences " << equiv);
		equiv.push_back(res);
		return FormulaT(carl::FormulaType::AND, std::move(equiv));
	}
}

#include "Instantiation.h"
