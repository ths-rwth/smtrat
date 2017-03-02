#pragma once

#include "../../../Common.h"
#include "../SolverTypes.h"

#include "VariableSelector.h"

#include <functional>
#include <map>
#include <vector>

namespace smtrat {
namespace mcsat {


class TheoryStack {
public:
private:
	const InformationGetter& mGetter;
	/**
	 * The first entry of the stack always contains an entry for the non-theory
	 * variables: the variable is set to NO_VARIABLE and the lists contain
	 * clauses and variables that do not contain any theory variables.
	 */
	using TheoryStackT = std::vector<TheoryLevel>;
	TheoryStackT mTheoryStack;
	std::size_t mCurrentLevel;
	
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
	
	
public:
	TheoryStack(const InformationGetter& ig):
		mGetter(ig),
		mTheoryStack(1, TheoryLevel()),
		mCurrentLevel(0)
	{}
	
	bool empty() const {
		return mCurrentLevel == 0;;
	}
	
	std::size_t level() const {
		return mCurrentLevel;
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
	
	void relocateClauses(Minisat::ClauseAllocator& from, Minisat::ClauseAllocator& to);
	
	// ***** Auxiliary getter
	
	/// Checks whether the given formula is univariate on the given level
	bool isFormulaUnivariate(const FormulaT& formula, std::size_t level) const;
	/// Checks whether the given clause is univariate on the given level
	bool isClauseUnivariate(Minisat::CRef clause, std::size_t level) const;
	/// Determines the level of the given variable
	std::size_t levelOfVariable(Minisat::Var var) {
		return mVariableLevelMap[std::size_t(var)];
	}
	
	// ***** Output
	/// Prints a single clause
	void printClause(std::ostream& os, Minisat::CRef clause) const;
	friend std::ostream& operator<<(std::ostream& os, const TheoryStack& mcts);
};

}
}
