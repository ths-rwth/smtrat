#pragma once

#include "Common.h"

#include "../SolverTypes.h"

#include "BaseBackend.h"
#include "../ClauseChecker.h"

#include <carl/formula/model/Assignment.h>

#include <functional>
#include <map>
#include <set>
#include <vector>

namespace smtrat {
namespace mcsat {

using carl::operator<<;
    
struct InformationGetter {
	std::function<Minisat::lbool(Minisat::Var)> getVarValue;
	std::function<Minisat::lbool(Minisat::Lit)> getLitValue;
	std::function<Minisat::lbool(Minisat::Var)> getBoolVarValue;
	std::function<int(Minisat::Var)> getDecisionLevel;
	std::function<int(Minisat::Var)> getTrailIndex;
	std::function<Minisat::CRef(Minisat::Var)> getReason;
	std::function<const Minisat::Clause&(Minisat::CRef)> getClause;
	std::function<const Minisat::vec<Minisat::CRef>&()> getClauses;
	std::function<const Minisat::vec<Minisat::CRef>&()> getLearntClauses;
	std::function<bool(Minisat::Var)> isTheoryAbstraction;
	std::function<bool(const FormulaT&)> isAbstractedFormula;
	std::function<Minisat::Var(const FormulaT&)> abstractVariable;
	std::function<const FormulaT&(Minisat::Var)> reabstractVariable;
	std::function<const FormulaT&(Minisat::Lit)> reabstractLiteral;
	std::function<const Minisat::vec<Minisat::Watcher>&(Minisat::Lit)> getWatches;
};
struct TheoryLevel {
	/// Theory variable for this level
	carl::Variable variable = carl::Variable::NO_VARIABLE;
	/// Literal that assigns this theory variable
	Minisat::Lit decisionLiteral = Minisat::lit_Undef;
	/// Boolean variables univariate in this theory variable
	std::vector<Minisat::Var> univariateVariables;
};

template<typename Settings>
class MCSATMixin {
  
private:
	InformationGetter mGetter;
	
	/**
	 * The first entry of the stack always contains an entry for the non-theory
	 * variables: the variable is set to NO_VARIABLE and the lists contain
	 * variables that do not contain any theory variables.
	 */
	using TheoryStackT = std::vector<TheoryLevel>;
	TheoryStackT mTheoryStack;
	/// The level for the next theory variable to be decided
	std::size_t mCurrentLevel = 0;

	/// Variables that are not univariate in any variable yet.
	std::vector<Minisat::Var> mUndecidedVariables;
	
	MCSATBackend<Settings> mBackend;

private:
	// ***** private helper methods
	
	/// Updates lookup for the current level
	void updateCurrentLevel(carl::Variable var);
	/// Remove lookups of the last level
	void removeLastLevel();
public:
	
	template<typename BaseModule>
	explicit MCSATMixin(BaseModule& baseModule):
		mGetter({
			[&baseModule](Minisat::Var v){ return baseModule.value(v); },
			[&baseModule](Minisat::Lit l){ return baseModule.value(l); },
			[&baseModule](Minisat::Var l){ return baseModule.bool_value(l); },
			[&baseModule](Minisat::Var v){ return baseModule.vardata[v].level; },
			[&baseModule](Minisat::Var v){ return baseModule.vardata[v].mTrailIndex; },
			[&baseModule](Minisat::Var v){ return baseModule.reason(v); },
			[&baseModule](Minisat::CRef c) -> const auto& { return baseModule.ca[c]; },
			[&baseModule]() -> const auto& { return baseModule.clauses; },
			[&baseModule]() -> const auto& { return baseModule.learnts; },
			[&baseModule](Minisat::Var v){ return (baseModule.mBooleanConstraintMap.size() > v) && (baseModule.mBooleanConstraintMap[v].first != nullptr); },
			[&baseModule](const FormulaT& f) { return baseModule.mConstraintLiteralMap.count(f) > 0; },
			[&baseModule](const FormulaT& f) { return var(baseModule.mConstraintLiteralMap.at(f).front()); },
			[&baseModule](Minisat::Var v) -> const auto& { return baseModule.mBooleanConstraintMap[v].first->reabstraction; },
			[&baseModule](Minisat::Lit l) -> const auto& { return sign(l) ? baseModule.mBooleanConstraintMap[var(l)].second->reabstraction : baseModule.mBooleanConstraintMap[var(l)].first->reabstraction; },
			[&baseModule](Minisat::Lit l) -> const auto& { return baseModule.watches[l]; }
		}),
		mTheoryStack(1, TheoryLevel())
	{}
	
	std::size_t level() const {
		return mCurrentLevel;
	}
	const Model& model() const {
		return mBackend.getModel();
	}
	/// Returns the respective theory level
	const TheoryLevel& get(std::size_t level) const {
		assert(level < mTheoryStack.size());
		return mTheoryStack[level];
	}
	/// Returns the current theory level
	const TheoryLevel& current() const {
		return mTheoryStack[level()];
	}
	TheoryLevel& current() {
		return mTheoryStack[level()];
	}
	/// Retrieve the current theory variable
	carl::Variable currentVariable() const {
		return variable(level());
	}
	carl::Variable variable(std::size_t level) const {
		SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Obtaining variable " << level << " from " << mBackend.variableOrder());
		if (level == 0) return carl::Variable::NO_VARIABLE;
		if (level > mBackend.variableOrder().size()) return carl::Variable::NO_VARIABLE;
		assert(level <= mBackend.variableOrder().size());
		return mBackend.variableOrder()[level - 1];
	}
	
	bool hasNextVariable() const {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Current level: " << level() << " with variables " << mBackend.variableOrder());
		return level() < mBackend.variableOrder().size();
	}
	carl::Variable nextVariable() const {
		assert(hasNextVariable());
		return mBackend.variableOrder()[level()];
	}
	bool mayDoAssignment() const {
		return current().variable != carl::Variable::NO_VARIABLE && current().decisionLiteral == Minisat::lit_Undef;
	}
	// ***** Modifier
	
	/// Advance to the next level using this variable
	void pushLevel(carl::Variable var);
	/// Retract one level (without removing the lookups)
	void popLevel();
	
	/**
	 * Add a new constraint.
	 */
	void doAssignment(Minisat::Lit lit) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Assigned " << lit);
		if (!mGetter.isTheoryAbstraction(var(lit))) return;
		const auto& f = mGetter.reabstractLiteral(lit);
		if (f.getType() == carl::FormulaType::VARASSIGN) {
			SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Skipping assignment.");
			return;
		}
		mBackend.pushConstraint(f);
	}
	/**
	 * Remove the last constraint. f must be the same as the one passed to the last call of pushConstraint().
	 */
	void undoAssignment(Minisat::Lit lit) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Unassigned " << lit);
		if (!mGetter.isTheoryAbstraction(var(lit))) return;
		const auto& f = mGetter.reabstractLiteral(lit);
		if (f.getType() == carl::FormulaType::VARASSIGN) {
			SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Skipping assignment.");
			return;
		}
		mBackend.popConstraint(f);
	}
	
	/// Add a variable, return the level it was inserted on
	std::size_t addVariable(Minisat::Var variable);

	// ***** Auxiliary getter
	
	/// Checks whether the given formula is univariate on the given level
	bool isFormulaUnivariate(const FormulaT& formula, std::size_t level) const;
	
	/// Make a decision and push a new level
	void makeDecision(Minisat::Lit decisionLiteral);
	/// Backtracks to the theory decision represented by the given literal. 
	bool backtrackTo(Minisat::Lit literal);
	
	// ***** Helper methods
	
	/// Evaluate a literal in the theory, set lastReason to last theory decision involved.
	Minisat::lbool evaluateLiteral(Minisat::Lit lit) const;
	
	// boost::optional<Explanation> isDecisionPossible(Minisat::Lit lit);
	bool isDecisionPossible(Minisat::Lit lit);
	
	boost::optional<Explanation> isFeasible() {
		if (!mayDoAssignment()) {
			SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Trail is feasible as there is no next variable to be assigned.");
			return boost::none;
		}
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Checking whether trail is feasible (w.r.t. " << currentVariable() << ")");
		auto res = mBackend.findAssignment(currentVariable());
		if (carl::variant_is_type<ModelValue>(res)) {
			return boost::none;
		} else {
			const auto& confl = boost::get<FormulasT>(res);
			SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Explaining " << confl);
			return mBackend.explain(currentVariable(), confl);
		}
	}
	
	std::pair<Explanation,bool> makeTheoryDecision() {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Obtaining assignment");
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", mBackend);
		auto res = mBackend.findAssignment(currentVariable());
		if (carl::variant_is_type<ModelValue>(res)) {
			const auto& value = boost::get<ModelValue>(res);
			SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "-> " << value);
			FormulaT repr = carl::representingFormula(currentVariable(), value);
			mBackend.pushAssignment(currentVariable(), value, repr);
			assert(trailIsConsistent());
			return std::make_pair(repr, true);
		} else {
			const auto& confl = boost::get<FormulasT>(res);
			auto explanation = mBackend.explain(currentVariable(), confl);
			SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Got a conflict: " << explanation);
			return std::make_pair(explanation, false);
		}
	}
	
	Explanation explainTheoryPropagation(Minisat::Lit literal) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Current state: " << (*this));
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Explaining " << literal << " under " << mBackend.getModel());
		const auto& f = mGetter.reabstractLiteral(literal);
		boost::optional<FormulasT> conflict = mBackend.isInfeasible(currentVariable(), !f);
		assert(conflict);
		(*conflict).push_back(!f);
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Explaining " << f << " from " << *conflict);
		auto res = mBackend.explain(currentVariable(), *conflict);
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Explaining " << f << " by " << res);
		// f is part of the conflict, because the trail is feasible without f:
		if (res.type() == typeid(FormulaT)) {
			assert(boost::get<FormulaT>(res).contains(f));
		}
		else {
			assert(boost::get<FormulasT>(res).back().contains(f)); // TODO rethink [if only one conflict is allowed, then this works]
		}
		return res;
	}
	
	template<typename Constraints>
	void resetVariableOrdering(const Constraints& c) {
		mBackend.resetVariableOrdering(c);
	}
	
	// ***** Auxliary getter
	
	/// Checks whether the given formula is currently univariate
	bool isFormulaUnivariate(const FormulaT& formula) const {
		return isFormulaUnivariate(formula, level());
	}
	
	std::size_t theoryLevel(Minisat::Var var) const {
		if (!mGetter.isTheoryAbstraction(var)) {
			return 0;
		}
		return theoryLevel(mGetter.reabstractVariable(var));
	}
	
	std::size_t theoryLevel(const FormulaT& f) const {
		SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Computing theory level for " << f);
		carl::Variables vars;
		f.arithmeticVars(vars);
		if (vars.empty()) {
			SMTRAT_LOG_TRACE("smtrat.sat.mcsat", f << " has no variable, thus on level 0");
			return 0;
		}
		
		//for (std::size_t lvl = level(); lvl > 0; lvl--) {
		//	if (variable(lvl) == carl::Variable::NO_VARIABLE) continue;
		//	if (vars.count(variable(lvl)) > 0) {
		//		SMTRAT_LOG_TRACE("smtrat.sat.mcsat", f << " is univariate in " << variable(lvl));
		//		return lvl;
		//	}
		//}
		//SMTRAT_LOG_TRACE("smtrat.sat.mcsat", f << " contains undecided variables.");
		//return std::numeric_limits<std::size_t>::max();
	
		Model m = model();
		if (!carl::model::evaluate(f, m).isBool()) {
			SMTRAT_LOG_TRACE("smtrat.sat.mcsat", f << " is undecided.");
			return std::numeric_limits<std::size_t>::max();
		}
		for (std::size_t lvl = level(); lvl > 0; lvl--) {
			if (variable(lvl) == carl::Variable::NO_VARIABLE) continue;
			m.erase(variable(lvl));
			if (vars.count(variable(lvl)) == 0) continue;
			if (!carl::model::evaluate(f, m).isBool()) {
				return lvl;
			}
		}
		assert(false);
		return 0;
		
		for (std::size_t level = 1; level < mTheoryStack.size(); level++) {
			vars.erase(variable(level));
			if (vars.empty()) {
				SMTRAT_LOG_TRACE("smtrat.sat.mcsat", f << " is univariate in " << variable(level));
				return level;
			}
		}
		SMTRAT_LOG_TRACE("smtrat.sat.mcsat", f << " is undecided.");
		return std::numeric_limits<std::size_t>::max();
	}
	
	Minisat::Lit getDecisionLiteral(Minisat::Var var) const {
		if (!mGetter.isTheoryAbstraction(var)) {
			return Minisat::lit_Undef;
		}
		return getDecisionLiteral(mGetter.reabstractVariable(var));
	}
	Minisat::Lit getDecisionLiteral(const FormulaT& f) const {
		std::size_t level = theoryLevel(f);
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Theory level of " << f << " is " << level);
		if (level >= mTheoryStack.size()) return Minisat::lit_Undef;
		return get(level).decisionLiteral;
	}
	
	int assignedAtTrailIndex(Minisat::Var variable) const {
		auto lit = getDecisionLiteral(variable);
		if (lit == Minisat::lit_Undef) {
			SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", variable << " was not assigned yet.");
			return std::numeric_limits<int>::max();
		}
		return mGetter.getTrailIndex(var(lit));
	}
	
	int decisionLevel(Minisat::Var var) const {
		if (!mGetter.isTheoryAbstraction(var)) {
			return std::numeric_limits<int>::max();
		}
		return decisionLevel(mGetter.reabstractVariable(var));
	}
	
	int decisionLevel(const FormulaT& f) const {
		auto lit = getDecisionLiteral(f);
		if (lit == Minisat::lit_Undef) {
			return std::numeric_limits<int>::max();
		}
		return mGetter.getDecisionLevel(var(lit));
	}
	
	bool trailIsConsistent() const {
		const auto& trail = mBackend.getTrail();
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Checking trail against " << trail.model());
		auto evaluator = [&trail](const auto& c){
			auto res = carl::model::evaluate(c, trail.model());
			SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", c << " evaluates to " << res);
			if (res.isBool()) {
				if (!res.asBool()) return false;
			}
			return true;
		};
		for (const auto& c: trail.constraints()) {
			auto category = mcsat::constraint_type::categorize(c, model(), carl::Variable::NO_VARIABLE);
			if (category != mcsat::constraint_type::ConstraintType::Assigned) continue;
			if (!evaluator(c)) return false;
		}
		for (const auto& b: trail.mvBounds()) {
			auto category = mcsat::constraint_type::categorize(b, model(), carl::Variable::NO_VARIABLE);
			if (category != mcsat::constraint_type::ConstraintType::Assigned) continue;
			if (!evaluator(b)) return false;
		}
		return true;
	}
	
	// ***** Output
	/// Prints a single clause
	void printClause(std::ostream& os, Minisat::CRef clause) const;
	template<typename Sett>
	friend std::ostream& operator<<(std::ostream& os, const MCSATMixin<Sett>& mcm);
};

}
}

#include "MCSATMixin.tpp"
