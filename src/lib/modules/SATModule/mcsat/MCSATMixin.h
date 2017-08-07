#pragma once

#include "../../../Common.h"

#include "../SolverTypes.h"

#include "VariableSelector.h"
#include "../../../datastructures/mcsat/nlsat.h"
#include "../../../datastructures/mcsat/nlsat/NLSAT.h"

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
	std::function<int(Minisat::Var)> getDecisionLevel;
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
	/// Clauses univariate in this theory variable
	std::vector<Minisat::CRef> univariateClauses;
	/// Boolean variables univariate in this theory variable
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
	/// The level for the next theory variable to be decided
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
	
	/// stores the reason for theory propagations. These are basically clauses, but not clauses from the minisat database.
	std::map<Minisat::Var,std::vector<Minisat::Lit>> mPropagationReasons;

	/// current mc-sat model
	Model mCurrentModel;
	
	nlsat::Explain<nlsat::LemmaStrategy::ORIGINAL> mExplain;
	
	nlsat::NLSAT mNLSAT;

private:
	// ***** private helper methods
	
	/// Updates lookup for the current level
	void updateCurrentLevel(carl::Variable var);
	/// Remove lookups of the last level
	void removeLastLevel();

	/// Store the level of a variable in mVariableLevelMap
	void setVariableLevel(Minisat::Var var, std::size_t level) {
		SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "level(" << var << ") = " << level);
		if (std::size_t(var) >= mVariableLevelMap.size()) {
			mVariableLevelMap.insert(mVariableLevelMap.end(), std::size_t(var) - mVariableLevelMap.size() + 1, 0);
		}
		mVariableLevelMap[std::size_t(var)] = level;
		SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "-> " << mVariableLevelMap);
	}
public:
	
	template<typename BaseModule>
	MCSATMixin(const BaseModule& baseModule):
		mGetter({
			[&baseModule](Minisat::Var v){ return baseModule.value(v); },
			[&baseModule](Minisat::Lit l){ return baseModule.value(l); },
			[&baseModule](Minisat::Var v){ return baseModule.vardata[v].level; },
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
		assert(std::size_t(var) < mVariableLevelMap.size());
		return mVariableLevelMap[std::size_t(var)];
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
		if (!mGetter.isTheoryAbstraction(var(lit))) return;
		const auto& f = mGetter.reabstractLiteral(lit);
		if (f.getType() == carl::FormulaType::VARASSIGN) {
			SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Skipping assignment.");
			return;
		}
		mNLSAT.pushConstraint(f);
	}
	/**
	 * Remove the last constraint. f must be the same as the one passed to the last call of pushConstraint().
	 */
	void undoAssignment(Minisat::Lit lit) {
		if (!mGetter.isTheoryAbstraction(var(lit))) return;
		const auto& f = mGetter.reabstractLiteral(lit);
		if (f.getType() == carl::FormulaType::VARASSIGN) {
			SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Skipping assignment.");
			return;
		}
		mNLSAT.popConstraint(f);
	}
	
	/// Add a variable, return the level it was inserted on
	std::size_t addVariable(Minisat::Var variable);
	
	/// Add a clause
	void addClause(Minisat::CRef clause);
	/// Remove a clause
	void removeClause(Minisat::CRef clause);
	
	/// Adapt to clause relocation of Minisat
	void relocateClauses(Minisat::ClauseAllocator& from, Minisat::ClauseAllocator& to);
	
	/// Try to propagate all boolean variables that are univariate
	bool performTheoryPropagations();
	
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
	
	boost::variant<Minisat::Lit,FormulaT> pickLiteralForDecision(); 
	
	std::pair<FormulaT,bool> makeTheoryDecision() {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Obtaining assignment");
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", mNLSAT);
		auto res = mNLSAT.findAssignment(currentVariable());
		if (carl::variant_is_type<ModelValue>(res)) {
			const auto& value = boost::get<ModelValue>(res);
			SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "-> " << value);
			FormulaT repr = carl::representingFormula(currentVariable(), value);
			mNLSAT.pushAssignment(currentVariable(), value, repr);
			return std::make_pair(repr, true);
		} else {
			const auto& confl = boost::get<FormulasT>(res);
			auto explanation = mNLSAT.explain(currentVariable(), confl, FormulaT(carl::FormulaType::FALSE));
			SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Got a conflict: " << explanation);
			return std::make_pair(explanation, false);
		}
	}
	
	// ***** Auxliary getter
	
	/// Check whether a literal is in a univariate clause, try to change the watch to a non-univariate literal.
	bool isLiteralInUnivariateClause(Minisat::Lit literal, const Minisat::vec<Minisat::CRef>& clauses);
	bool isLiteralInUnivariateClause(Minisat::Lit literal);
	
	/// Checks whether the given formula is currently univariate
	bool isFormulaUnivariate(const FormulaT& formula) const {
		return isFormulaUnivariate(formula, mCurrentLevel);
	}
	
	std::size_t computeVariableLevel(Minisat::Var variable) const;
	
	/**
	 * Compute the penultimate relevant decision level for the given formula.
	 * This is used to determine the level to backtrack to if f is a conflict clause.
	 * If a literal was assigned by boolean decision or propagation, this level is to be used.
	 */
	std::size_t penultimateTheoryLevel(const FormulaT& f) const {
		const auto& formulas = f.isNary() ? f.subformulas() : FormulasT({f});
		std::vector<std::size_t> levels;
		for (const auto& formula: formulas) {
			// Figure out whether formula is false from boolean or theory assignment 
			boost::optional<Minisat::Var> decisionVar;
			if (mGetter.isAbstractedFormula(formula)) {
				auto minisatvar = mGetter.abstractVariable(formula);
				if (mGetter.getVarValue(minisatvar) != l_Undef) {
					decisionVar = minisatvar;
				}
			}
			if (decisionVar) {
				levels.push_back(mGetter.getDecisionLevel(*decisionVar) - 1);
				SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", formula << " becomes unassigned at " << levels.back());
			} else {
				carl::Variables vars;
				formula.arithmeticVars(vars);
				for (std::size_t lvl = level()-1; lvl > 0; lvl--) {
					if (vars.find(get(lvl).variable) != vars.end()) {
						Minisat::Lit declit = get(lvl).decisionLiteral;
						if (declit != Minisat::lit_Undef) {
							levels.push_back(mGetter.getDecisionLevel(var(declit)) - 1);
							SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", formula << " becomes unassigned at " << levels.back());
						}
					}
				}
			}
		}
		
		auto res = *std::max_element(levels.begin(), levels.end());
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "-> returning " << res);
		return res;
		
		carl::Variables vars;
		f.arithmeticVars(vars);
		assert(vars.find(current().variable) != vars.end());
		for (std::size_t lvl = level()-1; lvl > 0; lvl--) {
			if (vars.find(get(lvl).variable) != vars.end()) {
				return lvl;
			}
		}
		return 0;
	}
	
	// ***** Output
	/// Prints a single clause
	void printClause(std::ostream& os, Minisat::CRef clause) const;
	friend std::ostream& operator<<(std::ostream& os, const MCSATMixin& mcm);
};

}
}
