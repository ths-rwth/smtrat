#include "MCSATMixin.h"

namespace smtrat {
namespace mcsat {

template<typename Settings>
void MCSATMixin<Settings>::makeDecision(Minisat::Lit decisionLiteral) {
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Made theory decision for " << currentVariable() << ": " << decisionLiteral);
	SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Variables: " << mBackend.variableOrder());
	current().decisionLiteral = decisionLiteral;
}

template<typename Settings>
bool MCSATMixin<Settings>::backtrackTo(Minisat::Lit literal) {
	std::size_t lvl = level();
	while (lvl > 0) {
		if (get(lvl).decisionLiteral == literal) break;
		lvl--;
	}
	SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Backtracking until " << literal << " on level " << lvl);
	if (lvl == 0 || lvl == level()) {
		SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Nothing to backtrack for " << literal);
		return false;
	}
	
	while (level() > lvl) {
		popLevel();
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Backtracking theory assignment for " << currentVariable());

		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Model " << model());

		if (current().decisionLiteral != Minisat::lit_Undef) {
			mBackend.popAssignment(currentVariable());
		}
		current().decisionLiteral = Minisat::lit_Undef;
	}
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Next theory variable is " << currentVariable());
	return true;
}

template<typename Settings>
Minisat::lbool MCSATMixin<Settings>::evaluateLiteral(Minisat::Lit lit) const {
	SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Evaluate " << lit);
	const FormulaT& f = mGetter.reabstractLiteral(lit);
	SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Evaluate " << f << " on " << mBackend.getModel());
	auto res = carl::model::evaluate(f, mBackend.getModel());
	if (res.isBool()) {
		return res.asBool() ? l_True : l_False;
	}
	return l_Undef;
}

/*
template<typename Settings>
boost::optional<Explanation> MCSATMixin<Settings>::isDecisionPossible(Minisat::Lit lit) {
	auto var = Minisat::var(lit);
	if (!mGetter.isTheoryAbstraction(var)) return boost::none;
	const auto& f = mGetter.reabstractLiteral(lit);
	auto res = mBackend.isInfeasible(currentVariable(), f);
	if (res == boost::none) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Decision " << lit << " is possible");
	} else {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Decision " << lit << " is impossible due to " << *res);
		return mBackend.explain(currentVariable(), *res);
	}
	return boost::none;
}
*/

template<typename Settings>
bool MCSATMixin<Settings>::isDecisionPossible(Minisat::Lit lit) {
	auto var = Minisat::var(lit);
	if (!mGetter.isTheoryAbstraction(var)) return true;
	const auto& f = mGetter.reabstractLiteral(lit);
	auto res = mBackend.isInfeasible(currentVariable(), f);
	if (res == boost::none) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Decision " << lit << " (" << f << ") is possible");
	} else {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Decision " << lit << " (" << f << ") is impossible due to " << *res);
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Current state: " << (*this));
		return false;
	}
	return true;
}

template<typename Settings>
void MCSATMixin<Settings>::updateCurrentLevel(carl::Variable var) {
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Updating current level for " << var);
	assert(level() <= mTheoryStack.size());
	if (level() == mTheoryStack.size()) {
		mTheoryStack.emplace_back();
		current().variable = var;
	} else {
		assert(current().variable == var);
	}
	
	// Check undecided variables whether they became univariate
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Undecided Variables: " << mUndecidedVariables);
	for (auto vit = mUndecidedVariables.begin(); vit != mUndecidedVariables.end();) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Looking at " << *vit);
		if (theoryLevel(*vit) != level()) {
			++vit;
			continue;
		}
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Associating " << *vit << " with " << var << " at " << level());
		current().univariateVariables.push_back(*vit);
		vit = mUndecidedVariables.erase(vit);
	}
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "-> " << mUndecidedVariables);
}

template<typename Settings>
void MCSATMixin<Settings>::removeLastLevel() {
	assert(!mTheoryStack.empty());
	assert(level() < mTheoryStack.size() - 1);
	
	mUndecidedVariables.insert(
		mUndecidedVariables.end(),
		mTheoryStack.back().univariateVariables.begin(),
		mTheoryStack.back().univariateVariables.end()
	);
	mTheoryStack.pop_back();
}

template<typename Settings>
void MCSATMixin<Settings>::pushLevel(carl::Variable var) {
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Pushing new level with " << var);
	// Future levels are cached and maybe should be discarded
	if (level() != mTheoryStack.size() - 1) {
		// Next level already has the right variable
		if (current().variable == var) return;
		// Discard levels until the current one
		while (level() != mTheoryStack.size() - 1) {
			removeLastLevel();
		}
	}
	mCurrentLevel++;
	// Push new level
	updateCurrentLevel(var);
}

template<typename Settings>
void MCSATMixin<Settings>::popLevel() {
	mCurrentLevel--;
}

template<typename Settings>
std::size_t MCSATMixin<Settings>::addVariable(Minisat::Var variable) {
	std::size_t level = theoryLevel(variable);
	if (level == std::numeric_limits<std::size_t>::max()) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Adding " << variable << " to undecided");
		mUndecidedVariables.push_back(variable);
	} else {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Adding " << variable << " on level " << level);
		mTheoryStack[level].univariateVariables.push_back(variable);
	}
	return level;
}

template<typename Settings>
bool MCSATMixin<Settings>::isFormulaUnivariate(const FormulaT& formula, std::size_t level) const {
	assert(level < mTheoryStack.size());
	carl::Variables vars;
	formula.arithmeticVars(vars);
	for (std::size_t lvl = 1; lvl <= level; lvl++) {
		vars.erase(variable(lvl));
	}
	SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Checking if " << formula << " is univariate on level " << level << ": " << vars.empty());
	return vars.empty();
}

template<typename Settings>
void MCSATMixin<Settings>::printClause(std::ostream& os, Minisat::CRef clause) const {
	const Minisat::Clause& c = mGetter.getClause(clause);
	os << "(";
	for (int i = 0; i < c.size(); i++) {
		if (i > 0) os << " ";
		if (mGetter.isTheoryAbstraction(var(c[i]))) {
			os << mGetter.reabstractLiteral(c[i]);
		} else {
			os << c[i];
		}
	}
	os << ")";
}

template<typename Settings>
std::ostream& operator<<(std::ostream& os, const MCSATMixin<Settings>& mcm) {
	os << "Theory Stack: " << mcm.level() << std::endl;
	for (std::size_t lvl = 0; lvl < mcm.mTheoryStack.size(); lvl++) {
		const auto& level = mcm.get(lvl);
		os << lvl << " / " << level.variable << " (" << level.decisionLiteral << ")";
		if (mcm.model().find(level.variable) != mcm.model().end()) {
			os << " = " << mcm.model().at(level.variable);
		}
		if (level.variable == mcm.current().variable) {
			os << " <<-- Current variable";
		}
		os << std::endl;
		os << "\tVariables: " << level.univariateVariables << std::endl;
	}
	os << "Backend:" << std::endl;
	os << mcm.mBackend << std::endl;
	return os;
}

}
}
