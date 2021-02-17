#include "MCSATMixin.h"

namespace smtrat {
namespace mcsat {

template<typename Settings>
void MCSATMixin<Settings>::pushTheoryDecision(const FormulaT& assignment, Minisat::Lit decisionLiteral) {
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Made theory decision for " << assignment.variableAssignment().var() << ": " << decisionLiteral);
	assert(mInconsistentVariables.empty());
	mBackend.pushAssignment( assignment.variableAssignment().var(),  assignment.variableAssignment().value(), assignment);
	mTheoryStack.emplace_back();
	current().variable = assignment.variableAssignment().var();
	current().decisionLiteral = decisionLiteral;
	updateCurrentLevel();
}

template<typename Settings>
void MCSATMixin<Settings>::popTheoryDecision() {
	assert(!mTheoryStack.empty());
	mUndecidedVariables.insert(
		mUndecidedVariables.end(),
		mTheoryStack.back().decidedVariables.begin(),
		mTheoryStack.back().decidedVariables.end()
	);
	for (const auto var : mTheoryStack.back().decidedVariables) {
		mTheoryLevels[varid(var)] = std::numeric_limits<std::size_t>::max();
		mSemanticPropagations.erase(var);
	}
	mTheoryStack.pop_back();
	mInconsistentVariables.clear();
	// mModelAssignmentCache.clear();
}

template<typename Settings>
void MCSATMixin<Settings>::updateCurrentLevel() {
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Updating current level " << current().variable);
	
	// Check undecided variables whether they became univariate
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Undecided Variables: " << mUndecidedVariables);
	for (auto vit = mUndecidedVariables.begin(); vit != mUndecidedVariables.end();) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Looking at " << *vit);
		/*if (computeTheoryLevel(*vit) != level()) {
			++vit;
			continue;
		}*/
		if (mGetter.isTheoryAbstraction(*vit)) {
			const auto& f = mGetter.reabstractVariable(*vit);
			auto evalres = carl::model::evaluate(f, model());
			if (!evalres.isBool()) {
				++vit;
				continue;
			} else if (mBackend.isActive(f) && mGetter.getBoolVarValue(*vit) != l_Undef && mGetter.getBoolVarValue(*vit) != Minisat::lbool(evalres.asBool())) {
				SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Found inconsistent variable " << *vit);
				mInconsistentVariables.push_back(*vit);
			}
		}
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Associating " << *vit << " with " << current().variable << " at " << level());
		current().decidedVariables.push_back(*vit);
		mTheoryLevels[varid(*vit)] = level();
		if (mGetter.getBoolVarValue(*vit) == l_Undef) {
			mSemanticPropagations.insert(*vit);
		}
		vit = mUndecidedVariables.erase(vit);
	}
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "-> " << mUndecidedVariables);
}

template<typename Settings>
bool MCSATMixin<Settings>::backtrackTo(Minisat::Lit literal) {
	std::size_t lvl = level();
	while (lvl > 0) {
		if (get(lvl).decisionLiteral == literal) break;
		lvl--;
	}
	SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Backtracking until " << literal << " on level " << lvl);
	if (lvl == 0) {
		SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Nothing to backtrack for " << literal);
		return false;
	}
	
	while (level() >= lvl) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Backtracking theory assignment for " << current().variable);

		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Model " << model());

		if (current().decisionLiteral != Minisat::lit_Undef) {
			mBackend.popAssignment(current().variable);
		}
		popTheoryDecision();
	}
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

/**
 * Checks is given literal is feasible with the current trail.
 */
template<typename Settings>
std::pair<bool, boost::optional<Explanation>> MCSATMixin<Settings>::isBooleanDecisionFeasible(Minisat::Lit lit, bool always_explain) {
	auto var = Minisat::var(lit);
	if (!mGetter.isTheoryAbstraction(var)) return std::make_pair(true, boost::none);
	const auto& f = mGetter.reabstractLiteral(lit);
	
	// assert that literal is consistent with the trail
	assert(evaluateLiteral(lit) != l_False);

	auto vars = carl::arithmetic_variables(f);
	for (const auto& v : mBackend.assignedVariables())
		vars.erase(v);
	
	if (vars.size() > 0) {
		carl::Variable tvar = *(vars.begin());

		auto res = mBackend.isInfeasible(tvar, f);
		if (carl::variant_is_type<ModelValues>(res)) {
			/* if (mModelAssignmentCache.empty()) {
				mModelAssignmentCache.cache(boost::get<ModelValues>(res));
			}*/
			SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Decision " << lit << " (" << f << ") is feasible wrt " << tvar);
			return std::make_pair(true, boost::none);
		} else {
			auto& confl = boost::get<FormulasT>(res);
			SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Decision " << lit << " (" << f << ") is infeasible wrt " << tvar << " due to " << confl);
			if (always_explain) {
				SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Explaining " << confl);
				return std::make_pair(false, mBackend.explain(tvar, confl));
			} else if (std::find(confl.begin(), confl.end(), f) == confl.end()) {
				SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Conflicting core " << confl << " is independent from decision " << f);
				return std::make_pair(false, mBackend.explain(tvar, confl));
			} else {
				SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Check if trail without " << f << " was feasible wrt " << tvar);
				auto expl = isFeasible(tvar);
				if (expl) {
					SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Trail without " << f << " was infeasible wrt " << tvar);
					return std::make_pair(false, std::move(*expl));
				} else {
					SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Infeasibility wrt " << tvar << " depends truly on " << f);
					return std::make_pair(false, boost::none);
				}
			}
		}
	} else {
	 	return std::make_pair(true, boost::none);
	}
}

template<typename Settings>
std::pair<boost::tribool, boost::optional<Explanation>> MCSATMixin<Settings>::propagateBooleanDomain(Minisat::Lit lit) {
	auto var = Minisat::var(lit);
	if (!mGetter.isTheoryAbstraction(var)) return std::make_pair(boost::indeterminate, boost::none);
	const auto& f = mGetter.reabstractLiteral(lit);
	
	auto vars = carl::arithmetic_variables(f);
	for (const auto& v : mBackend.assignedVariables())
		vars.erase(v);
	
	assert(vars.size() > 0);

	carl::Variable tvar = *(vars.begin());

	auto res_pos = mBackend.isInfeasible(tvar, f);
	auto res_neg = mBackend.isInfeasible(tvar, f.negated());

	if (carl::variant_is_type<ModelValues>(res_pos) && carl::variant_is_type<ModelValues>(res_neg)) {
		/* if (mModelAssignmentCache.empty()) {
			mModelAssignmentCache.cache(boost::get<ModelValues>(res));
		}*/
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Decision: " << lit << " (" << f << ") and its negation are feasible wrt " << tvar);
		return std::make_pair(boost::indeterminate, boost::none);
	} else if (carl::variant_is_type<ModelValues>(res_pos)) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Propagation: " << lit << " (" << f << ") is feasible wrt " << tvar);
		return std::make_pair(true, boost::none);
	} else if (carl::variant_is_type<ModelValues>(res_neg)) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Propagation: negation of " << lit << " (" << f << ") is feasible wrt " << tvar);
		return std::make_pair(false, boost::none);
	} else {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Conflict: " << lit << " (" << f << ") and its negation are infeasible wrt " << tvar << " due to " << boost::get<FormulasT>(res_pos) << " resp. " << boost::get<FormulasT>(res_neg));

		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Check if trail without " << f << " was feasible wrt " << tvar);
		auto expl = isFeasible(tvar);
		assert(expl);
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Trail without " << f << " was infeasible wrt " << tvar);
		return std::make_pair(boost::indeterminate, std::move(*expl));
	}
}

template<typename Settings>
std::size_t MCSATMixin<Settings>::addBooleanVariable(Minisat::Var variable) {
	while (mVarPropertyCache.size() <= varid(variable)) {
		mVarPropertyCache.emplace_back();
	}

	while (mTheoryLevels.size() <= varid(variable)) {
		mTheoryLevels.emplace_back();
	}

	std::size_t level = computeTheoryLevel(variable);
	if (!mGetter.isTheoryAbstraction(variable)) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Ignoring " << variable << " as it is not a theory abstraction");
		return level;
	}
	assert(mGetter.reabstractVariable(variable).getType() != carl::FormulaType::VARASSIGN);
	if (level == std::numeric_limits<std::size_t>::max()) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Adding " << variable << " to undecided");
		mUndecidedVariables.push_back(variable);
		mTheoryLevels[varid(variable)] = std::numeric_limits<std::size_t>::max();
	} else {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Adding " << variable << " on level " << level);
		mTheoryStack[level].decidedVariables.push_back(variable);
		mTheoryLevels[varid(variable)] = level;
		mSemanticPropagations.insert(variable);
	}
	return level;
}

template<typename Settings>
bool MCSATMixin<Settings>::isFormulaUnivariate(const FormulaT& formula, std::size_t level) const {
	assert(level < mTheoryStack.size());
	auto vars = carl::arithmetic_variables(formula);
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
		// if (level.variable == mcm.current().variable) {
		//	os << " <<-- Current variable";
		// }
		os << std::endl;
		os << "\tVariables: " << level.decidedVariables << std::endl;
	}
	os << "Backend:" << std::endl;
	os << mcm.mBackend << std::endl;
	os << "Theory variable mapping:" << std::endl;
	os << mcm.mTheoryVarMapping.minisatToCarl << std::endl;
	return os;
}

}
}
