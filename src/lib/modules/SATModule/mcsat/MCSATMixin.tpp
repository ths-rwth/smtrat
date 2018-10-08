#include "MCSATMixin.h"

namespace smtrat {
namespace mcsat {

template<typename Settings>
void MCSATMixin<Settings>::makeDecision(Minisat::Lit decisionLiteral) {
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Made theory decision for " << currentVariable() << ": " << decisionLiteral);
	SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Variables: " << mBackend.variableOrder());
	current().decisionLiteral = decisionLiteral;
	updateCurrentLevel();
}

template<typename Settings>
void MCSATMixin<Settings>::undoDecision() {
	current().decisionLiteral = Minisat::lit_Undef;
	mUndecidedVariables.insert(
		mUndecidedVariables.end(),
		mTheoryStack.back().univariateVariables.begin(),
		mTheoryStack.back().univariateVariables.end()
	);
	mTheoryStack.back().univariateVariables.clear();
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
		undoDecision();
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

template<typename Settings>
std::pair<bool, boost::optional<Explanation>> MCSATMixin<Settings>::isDecisionPossible(Minisat::Lit lit, bool check_feasibility_before) {
	auto var = Minisat::var(lit);
	if (!mGetter.isTheoryAbstraction(var)) return std::make_pair(true, boost::none);
	const auto& f = mGetter.reabstractLiteral(lit);
	auto res = mBackend.isInfeasible(currentVariable(), f);
	if (carl::variant_is_type<ModelValues>(res)) {
		if (mModelAssignmentCache.empty()) {
			mModelAssignmentCache = boost::get<ModelValues>(res);
		}
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Decision " << lit << " (" << f << ") is possible");
		return std::make_pair(true, boost::none);
	} else {
		auto& confl = boost::get<FormulasT>(res);
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Decision " << lit << " (" << f << ") is impossible due to " << confl);
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Current state: " << (*this));
		if (check_feasibility_before) {
			if (std::find(confl.begin(), confl.end(), f) == confl.end()) {
				SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Conflicting core " << confl << " is independent from decision " << f);
				return std::make_pair(false, mBackend.explain(currentVariable(), confl));
			} else {
				SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Check if trail without " << f << " was feasible");
				auto expl = isFeasible();
				if (expl) {
					SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Trail without " << f << " was infeasible");
					return std::make_pair(false, std::move(*expl));
				} else {
					SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Conflict depends truly on " << f);
					return std::make_pair(false, boost::none);
				}
			}
		} else {
			SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Explaining " << f << " from " << confl);
			return std::make_pair(false, mBackend.explain(currentVariable(), confl));
		}
	}
}

template<typename Settings>
void MCSATMixin<Settings>::updateCurrentLevel() {
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Updating current level " << current().variable);
	
	// Check undecided variables whether they became univariate
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Undecided Variables: " << mUndecidedVariables);
	for (auto vit = mUndecidedVariables.begin(); vit != mUndecidedVariables.end();) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Looking at " << *vit);
		if (theoryLevel(*vit) != level()) {
			++vit;
			continue;
		}
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Associating " << *vit << " with " << current().variable << " at " << level());
		current().univariateVariables.push_back(*vit);
		vit = mUndecidedVariables.erase(vit);
	}
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "-> " << mUndecidedVariables);
}

template<typename Settings>
void MCSATMixin<Settings>::pushLevel(carl::Variable var) {
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Pushing new level with " << var);
	mTheoryStack.emplace_back();
	current().variable = var;
}

template<typename Settings>
void MCSATMixin<Settings>::popLevel() {
	assert(!mTheoryStack.empty());
	assert(mTheoryStack.back().univariateVariables.empty());
	mTheoryStack.pop_back();
}

template<typename Settings>
std::size_t MCSATMixin<Settings>::addVariable(Minisat::Var variable) {
	while (mMaxTheoryLevel.size() <= variable) {
		mMaxTheoryLevel.push_back(std::numeric_limits<std::size_t>::max());
	}

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
