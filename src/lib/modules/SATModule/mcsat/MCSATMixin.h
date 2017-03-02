#pragma once

#include "../../../Common.h"

#include "../SolverTypes.h"

#include "VariableSelector.h"

#include <carl/formula/model/Assignment.h>

#include <functional>
#include <map>
#include <set>
#include <vector>

namespace smtrat {
namespace mcsat {

struct InformationGetter {
	std::function<Minisat::lbool(Minisat::Var)> getVarValue;
	std::function<Minisat::lbool(Minisat::Lit)> getLitValue;
	std::function<const Minisat::Clause&(Minisat::CRef)> getClause;
	std::function<bool(Minisat::Var)> isTheoryAbstraction;
	std::function<const FormulaT&(Minisat::Var)> reabstractVariable;
	std::function<const FormulaT&(Minisat::Lit)> reabstractLiteral;
	std::function<const Minisat::vec<Minisat::Watcher>&(Minisat::Lit)> getWatches;
};
struct TheoryLevel {
	carl::Variable variable = carl::Variable::NO_VARIABLE;
	Minisat::Lit decisionLiteral = Minisat::lit_Undef;
	std::vector<Minisat::CRef> univariateClauses;
	std::vector<Minisat::Var> univariateVariables;
};

class MCSATMixin {
private:
	InformationGetter mGetter;
	
	/**
	 * The first entry of the stack always contains an entry for the non-theory
	 * variables: the variable is set to NO_VARIABLE and the lists contain
	 * clauses and variables that do not contain any theory variables.
	 */
	using TheoryStackT = std::vector<TheoryLevel>;
	TheoryStackT mTheoryStack;
	std::size_t mCurrentLevel = 0;
	
	/// Clauses that are not univariate in any variable yet.
	std::vector<Minisat::CRef> mUndecidedClauses;
	/// Variables that are not univariate in any variable yet.
	std::vector<Minisat::Var> mUndecidedVariables;
	
	/// maps clauses to the level that they are univariate in
	std::map<Minisat::CRef,std::size_t> mClauseLevelMap;
	/// maps variables to the level that they are univariate in
	std::vector<std::size_t> mVariableLevelMap;

	/// takes care of selecting the next variable
	VariableSelector mVariables;

	/// current mc-sat model
	Model mCurrentModel;

private:
	// ***** private helper methods
	
	/// Updates lookup for the current level
	void updateCurrentLevel(carl::Variable var);
	/// Remove lookups of the last level
	void removeLastLevel();

	/// Store the level of a variable in mVariableLevelMap
	void setVariableLevel(Minisat::Var var, std::size_t level) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mc", "level(" << var << ") = " << level);
		while (int(mVariableLevelMap.size()) < var - 1) {
			mVariableLevelMap.push_back(0);
		}
		mVariableLevelMap[std::size_t(var)] = level;
		SMTRAT_LOG_DEBUG("smtrat.sat.mc", "-> " << mVariableLevelMap);
	}
public:
	
	template<typename BaseModule>
	MCSATMixin(const BaseModule& baseModule):
		mGetter({
			[&baseModule](Minisat::Var v){ return baseModule.value(v); },
			[&baseModule](Minisat::Lit l){ return baseModule.value(l); },
			[&baseModule](Minisat::CRef c) -> const auto& { return baseModule.ca[c]; },
			[&baseModule](Minisat::Var v){ return baseModule.mBooleanConstraintMap[v].first != nullptr; },
			[&baseModule](Minisat::Var v) -> const auto& { return baseModule.mBooleanConstraintMap[v].first->reabstraction; },
			[&baseModule](Minisat::Lit l) -> const auto& { return sign(l) ? baseModule.mBooleanConstraintMap[var(l)].second->reabstraction : baseModule.mBooleanConstraintMap[var(l)].first->reabstraction; },
			[&baseModule](Minisat::Lit l) -> const auto& { return baseModule.watches[l]; }
		}),
		mTheoryStack(1, TheoryLevel())
	{}
	
	// ***** simple getters
	bool empty() const {
		return mCurrentLevel == 0;;
	}
	
	std::size_t level() const {
		return mCurrentLevel;
	}
	const Model& model() const {
		return mCurrentModel;
	}
	/// Returns the respective theory level
	const TheoryLevel& get(std::size_t level) const {
		assert(level < mTheoryStack.size());
		return mTheoryStack[level];
	}
	/// Returns the current theory level
	const TheoryLevel& current() const {
		return mTheoryStack[mCurrentLevel];
	}
	TheoryLevel& current() {
		return mTheoryStack[mCurrentLevel];
	}
	/// Retrieve the current theory variable
	carl::Variable currentVariable() const {
		return current().variable;
	}
	/// Determines the level of the given variable
	std::size_t levelOfVariable(Minisat::Var var) {
		return mVariableLevelMap[std::size_t(var)];
	}
	
	// ***** Modifier
	
	/// Advance to the next level using this variable
	void pushLevel(carl::Variable var);
	/// Retract one level (without removing the lookups)
	void popLevel();
	
	/// Add a variable, return the level it was inserted on
	std::size_t addVariable(Minisat::Var variable);
	
	/// Add a clause
	void addClause(Minisat::CRef clause);
	/// Remove a clause
	void removeClause(Minisat::CRef clause);
	
	/// Adapt to clause relocation of Minisat
	void relocateClauses(Minisat::ClauseAllocator& from, Minisat::ClauseAllocator& to);
	
	// ***** Auxiliary getter
	
	/// Checks whether the given formula is univariate on the given level
	bool isFormulaUnivariate(const FormulaT& formula, std::size_t level) const;
	/// Checks whether the given clause is univariate on the given level
	bool isClauseUnivariate(Minisat::CRef clause, std::size_t level) const;
	
	/// Updates the model. If the current theory variable is not set, use the given default value
	void updateModel(const Model& model, const ModelValue& defaultValue) {
		mCurrentModel = model;
		if (mCurrentModel.find(currentVariable()) == mCurrentModel.end()) {
			mCurrentModel.assign(currentVariable(), defaultValue);
		}
	}
	
	bool hasNextVariable() {
		return !mVariables.empty();
	}
	carl::Variable nextVariable() {
		return mVariables.top();
	}
	/// Make a decision and push a new level
	void makeDecision(Minisat::Lit decisionLiteral);
	/// Backtracks to the theory decision represented by the given literal. 
	bool backtrackTo(Minisat::Lit literal);
	
	// ***** Helper methods
	
	FormulaT buildDecisionFormula() const {
		auto it = mCurrentModel.find(currentVariable());
		assert(it != mCurrentModel.end());
		FormulaT f = carl::representingFormula(currentVariable(), it->second);
		assert(f.getType() == carl::FormulaType::VARASSIGN);
		return f;
	}
	
	/// Evaluate a literal in the theory, set lastReason to last theory decision involved.
	Minisat::lbool evaluateLiteral(Minisat::Lit lit) const;
	
	Minisat::Lit pickLiteralForDecision();
	
	// ***** Auxliary getter
	
	/// Check whether a literal is in a univariate clause, try to change the watch to a non-univariate literal.
	bool isLiteralInUnivariateClause(Minisat::Lit literal);
	
	/// Checks whether the given formula is currently univariate
	bool isFormulaUnivariate(const FormulaT& formula) const {
		return isFormulaUnivariate(formula, mCurrentLevel);
	}
	
	std::size_t computeVariableLevel(Minisat::Var variable) const;
	
	// ***** Output
	/// Prints a single clause
	void printClause(std::ostream& os, Minisat::CRef clause) const;
	friend std::ostream& operator<<(std::ostream& os, const MCSATMixin& mcm);
};

}
}
