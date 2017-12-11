#include "MCSATMixin.h"

namespace smtrat {
namespace mcsat {

void MCSATMixin::makeDecision(Minisat::Lit decisionLiteral) {
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Made theory decision for " << current().variable << ": " << decisionLiteral);
	SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Variables: " << mVariables);
	current().decisionLiteral = decisionLiteral;
	mVariables.assign(current().variable);
}

bool MCSATMixin::backtrackTo(Minisat::Lit literal) {
	std::size_t level = mCurrentLevel;
	while (level > 0) {
		if (get(level).decisionLiteral == literal) break;
		level--;
	}
	SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Backtracking until " << literal << " on level " << level);
	if (level == 0 || level == mCurrentLevel) {
		SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Nothing to backtrack for " << literal);
		return false;
	}
	
	while (mCurrentLevel > level) {
		popLevel();
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Backtracking theory assignment for " << current().variable);

		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Model " << model());

		if (current().decisionLiteral != Minisat::lit_Undef) {
			mBackend.popAssignment(current().variable);
			mVariables.unassign(current().variable);
		}
	}
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Next theory variable is " << current().variable);
	return true;
}

Minisat::lbool MCSATMixin::evaluateLiteral(Minisat::Lit lit) const {
	SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Evaluate " << lit);
	const FormulaT& f = mGetter.reabstractLiteral(lit);

	SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Evaluate " << f << " on " << model());
	auto res = carl::model::evaluate(f, model());
	if (res.isBool()) {
		return res.asBool() ? l_True : l_False;
	}
	return l_Undef;
}

boost::variant<Minisat::Lit,FormulaT> MCSATMixin::checkLiteralForDecision(Minisat::Var var, Minisat::Lit lit) {
	if (!mGetter.isTheoryAbstraction(var)) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Returning boolean literal " << lit);
		return lit;
	}
	const auto& f = mGetter.reabstractLiteral(lit);
	auto res = mBackend.isInfeasible(currentVariable(), f);
	if (res == boost::none) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Returning feasible theory literal " << lit);
		return lit;
	} else {
		// There is a conflict. Return conflict. 
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Returning theory propagation for " << lit);
		return mBackend.explain(currentVariable(), *res, FormulaT(carl::FormulaType::FALSE));
		// Perform theory propagation (in search)
	}
}

Minisat::Lit MCSATMixin::isFullyAssigned(Minisat::Lit lit) {
	auto var = Minisat::var(lit);
	if (!mGetter.isTheoryAbstraction(var)) return Minisat::lit_Undef;
	const auto& f = mGetter.reabstractLiteral(lit);
	
	if (mcsat::constraint_type::isAssigned(f, model())) {
		FormulaT res(carl::model::substitute(f, model()));
		if (res.isTrue()) return lit;
		assert(res.isFalse());
		return neg(lit);
	}
	return Minisat::lit_Undef;
}

boost::optional<FormulaT> MCSATMixin::isDecisionPossible(Minisat::Lit lit) {
	auto var = Minisat::var(lit);
	if (!mGetter.isTheoryAbstraction(var)) return boost::none;
	const auto& f = mGetter.reabstractLiteral(lit);
	auto res = mBackend.isInfeasible(currentVariable(), f);
	if (res == boost::none) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Decision " << lit << " is possible");
	} else {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Decision " << lit << " is impossible due to " << *res);
		return mBackend.explain(currentVariable(), *res, FormulaT(carl::FormulaType::FALSE));
	}
	return boost::none;
}

void MCSATMixin::updateCurrentLevel(carl::Variable var) {
	SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Updating current level for " << var);
	assert(mCurrentLevel <= mTheoryStack.size());
	if (mCurrentLevel == mTheoryStack.size()) {
		mTheoryStack.emplace_back();
		current().variable = var;
	} else {
		assert(current().variable == var);
	}
	
	// Check undecided clauses whether they became univariate
	SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Undecided clauses: " << mUndecidedClauses);
	for (auto cit = mUndecidedClauses.begin(); cit != mUndecidedClauses.end();) {
		if (!isClauseUnivariate(*cit, mCurrentLevel)) {
			SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Skipping " << *cit << ": not univariate");
			cit++;
			continue;
		}
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Associating " << *cit << " with " << var << " at " << level());
		mClauseLevelMap[*cit] = mCurrentLevel;
		current().univariateClauses.push_back(*cit);
		cit = mUndecidedClauses.erase(cit);
	}
	SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "-> " << mUndecidedClauses);
	
	// Check undecided variables whether they became univariate
	SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Undecided Variables: " << mUndecidedVariables);
	for (auto vit = mUndecidedVariables.begin(); vit != mUndecidedVariables.end();) {
		SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Looking at " << *vit);
		std::size_t level = computeVariableLevel(*vit);
		if (level != mCurrentLevel) {
			vit++;
			continue;
		}
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Associating " << *vit << " with " << var << " at " << mCurrentLevel);
		current().univariateVariables.push_back(*vit);
		vit = mUndecidedVariables.erase(vit);
	}
	SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "-> " << mUndecidedVariables);
}

void MCSATMixin::removeLastLevel() {
	assert(!mTheoryStack.empty());
	assert(mCurrentLevel < mTheoryStack.size() - 1);
	for (auto c: mTheoryStack.back().univariateClauses) {
		mClauseLevelMap[c] = 0;
	}
	mUndecidedClauses.insert(
		mUndecidedClauses.end(),
		mTheoryStack.back().univariateClauses.begin(),
		mTheoryStack.back().univariateClauses.end()
	);
	mUndecidedVariables.insert(
		mUndecidedVariables.end(),
		mTheoryStack.back().univariateVariables.begin(),
		mTheoryStack.back().univariateVariables.end()
	);
	mTheoryStack.pop_back();
}

void MCSATMixin::pushLevel(carl::Variable var) {
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Pushing new level with " << var);
	// Future levels are cached and maybe should be discarded
	if (mCurrentLevel != mTheoryStack.size() - 1) {
		// Next level already has the right variable
		if (current().variable == var) return;
		// Discard levels until the current one
		while (mCurrentLevel != mTheoryStack.size() - 1) {
			removeLastLevel();
		}
	}
	mCurrentLevel++;
	// Push new level
	updateCurrentLevel(var);
}

void MCSATMixin::popLevel() {
	mCurrentLevel--;
}

std::size_t MCSATMixin::addVariable(Minisat::Var variable) {
	if (mGetter.isTheoryAbstraction(variable)) {
		mVariables.add(mGetter.reabstractVariable(variable));
	}
	std::size_t level = computeVariableLevel(variable);
	if (level == std::numeric_limits<std::size_t>::max()) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Adding " << variable << " to undecided");
		mUndecidedVariables.push_back(variable);
	} else {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Adding " << variable << " on level " << level);
		mTheoryStack[level].univariateVariables.push_back(variable);
	}
	return level;
}

void MCSATMixin::addClause(Minisat::CRef clause) {
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Adding " << clause);
	for (std::size_t level = 1; level < mTheoryStack.size(); level++) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Checking if " << clause << " is univariate in " << mTheoryStack[level].variable);
		if (isClauseUnivariate(clause, level)) {
			SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", clause << " is univariate in " << mTheoryStack[level].variable);
			mTheoryStack[level].univariateClauses.push_back(clause);
			mClauseLevelMap.emplace(clause, level);
			return;
		}
	}
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", clause << " was not found to be univariate, adding to undecided.");
	mUndecidedClauses.push_back(clause);
	mClauseLevelMap.emplace(clause, 0);
}

void MCSATMixin::removeClause(Minisat::CRef clause) {
	auto it = mClauseLevelMap.find(clause);
	SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Erasing " << clause << " from level " << it->second);
	auto& clist = mTheoryStack[it->second].univariateClauses;
	clist.erase(std::find(clist.begin(), clist.end(), clause));
	mClauseLevelMap.erase(it);
}

void MCSATMixin::relocateClauses(Minisat::ClauseAllocator& from, Minisat::ClauseAllocator& to) {
	for (auto& level: mTheoryStack) {
		for (auto& c: level.univariateClauses) {
			from.reloc(c, to);
		}
	}
	for (auto& c: mUndecidedClauses) {
		from.reloc(c, to);
	}
	std::map<Minisat::CRef,std::size_t> tmp;
	for (const auto& cl: mClauseLevelMap) {
		Minisat::CRef c = cl.first;
		from.reloc(c, to);
		tmp.emplace(c, cl.second);
	}
	mClauseLevelMap = std::move(tmp);
}

bool MCSATMixin::isFormulaUnivariate(const FormulaT& formula, std::size_t level) const {
	assert(level < mTheoryStack.size());
	carl::Variables vars;
	formula.arithmeticVars(vars);
	for (std::size_t lvl = 1; lvl <= level; lvl++) {
		vars.erase(get(lvl).variable);
		
	}
	SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Checking if " << formula << " is univariate on level " << level << ": " << vars.empty());
	return vars.empty();
}

bool MCSATMixin::isClauseUnivariate(Minisat::CRef clause, std::size_t level) const {
	const Minisat::Clause& c = mGetter.getClause(clause);
	for (int i = 0; i < c.size(); i++) {
		if (!mGetter.isTheoryAbstraction(var(c[i]))) continue;
		if (!isFormulaUnivariate(mGetter.reabstractVariable(var(c[i])), level)) {
			return false;
		}
	}
	return true;
}

std::size_t MCSATMixin::computeVariableLevel(Minisat::Var variable) const {
	if (!mGetter.isTheoryAbstraction(variable)) {
		SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Variable " << variable << " is not a theory abstraction, thus on level 0");
		return 0;
	}
	const FormulaT& f = mGetter.reabstractVariable(variable);
	carl::Variables vars;
	f.arithmeticVars(vars);
	if (vars.empty()) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mcsat", "Variable " << variable << " / " << f << " has no variable, thus on level 0");
		return 0;
	}
	for (std::size_t level = 1; level < mTheoryStack.size(); level++) {
		vars.erase(get(level).variable);
		if (vars.empty()) {
			SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Variable " << variable << " / " << f << " is univariate in " << get(level).variable);
			return level;
		}
	}
	SMTRAT_LOG_TRACE("smtrat.sat.mcsat", "Variable " << variable << " is undecided.");
	return std::numeric_limits<std::size_t>::max();
}

void MCSATMixin::printClause(std::ostream& os, Minisat::CRef clause) const {
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

std::ostream& operator<<(std::ostream& os, const MCSATMixin& mcm) {
	os << "Theory Stack:" << std::endl;
	for (std::size_t lvl = 0; lvl < mcm.mTheoryStack.size(); lvl++) {
		const auto& level = mcm.mTheoryStack[lvl];
		os << lvl << " / " << level.variable << " (" << level.decisionLiteral << ")";
		if (mcm.model().find(level.variable) != mcm.model().end()) {
			os << " = " << mcm.model().at(level.variable);
		}
		if (level.variable == mcm.current().variable) {
			os << " <<-- Current variable";
		}
		os << std::endl;
		os << "\tClauses:";
		for (const auto& c: level.univariateClauses) {
			os << " ";
			mcm.printClause(os, c);
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
