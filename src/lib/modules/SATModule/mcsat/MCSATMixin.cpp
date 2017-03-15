#include "MCSATMixin.h"

namespace smtrat {
namespace mcsat {

using carl::operator<<;

void MCSATMixin::makeDecision(Minisat::Lit decisionLiteral) {
	current().decisionLiteral = decisionLiteral;
	pushLevel(current().variable);
}

bool MCSATMixin::backtrackTo(Minisat::Lit literal) {
	std::size_t level = mCurrentLevel;
	while (level > 0) {
		if (get(level).decisionLiteral == literal) break;
		level--;
	}
	if (level == 0 || level == mCurrentLevel) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Nothing to backtrack for " << literal);
		return false;
	}
	
	while (mCurrentLevel > level) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Backtracking theory assignment for " << current().variable);
		auto it = mCurrentModel.find(current().variable);
		assert(it != mCurrentModel.end());
		mCurrentModel.erase(it);
		popLevel();
	}
	SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Next theory variable is " << current().variable);
	return true;
}

Minisat::lbool MCSATMixin::evaluateLiteral(Minisat::Lit lit) const {
	SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Evaluate " << lit);
	FormulaT f = mGetter.reabstractLiteral(lit);
	auto res = carl::model::evaluate(f, mCurrentModel);
	if (res.isBool()) {
		return res.asBool() ? l_True : l_False;
	}
	return l_Undef;
}

Minisat::Lit MCSATMixin::pickLiteralForDecision() {
	const auto& variables = current().univariateVariables;
	SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Univariate variables: " << variables);
	for (auto var: variables) {
		if (mGetter.getVarValue(var) != l_Undef) {
			SMTRAT_LOG_DEBUG("smtrat.sat.mc", var << " is already assigned.");
			continue;
		}
		SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Checking if " << var << " can be decided...");
		if (isLiteralInUnivariateClause(Minisat::mkLit(var, false))) {
			return Minisat::mkLit(var, false);
		}
		if (isLiteralInUnivariateClause(Minisat::mkLit(var, true))) {
			return Minisat::mkLit(var, true);
		}
	}
	return Minisat::lit_Undef;
}

bool MCSATMixin::isLiteralInUnivariateClause(Minisat::Lit literal) {
	for (int i = 0; i < mGetter.getWatches(literal).size(); i++) {
		const auto& watcher = mGetter.getWatches(literal)[i];
		SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Watch: " << watcher);
		auto cref = watcher.cref;
		auto blocker = watcher.blocker;
		if (mGetter.getLitValue(blocker) == l_True) continue;
		if (mGetter.getLitValue(blocker) == l_False) {
			// Check if there is another undecided, non-univariate literal in this clause
			if (levelOfVariable(var(blocker)) == 0) continue;
		}
	}
	return false;
}


void MCSATMixin::updateCurrentLevel(carl::Variable var) {
	SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Updating current level for " << var);
	assert(mCurrentLevel <= mTheoryStack.size());
	if (mCurrentLevel == mTheoryStack.size()) {
		mTheoryStack.emplace_back();
		current().variable = var;
	} else {
		assert(current().variable == var);
	}
	
	// Check undecided clauses whether they became univariate
	SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Undecided clauses: " << mUndecidedClauses);
	for (auto cit = mUndecidedClauses.begin(); cit != mUndecidedClauses.end();) {
		if (!isClauseUnivariate(*cit, mCurrentLevel)) {
			SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Skipping " << *cit << ": not univariate");
			cit++;
			continue;
		}
		SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Associating " << *cit << " with " << var);
		mClauseLevelMap[*cit] = mCurrentLevel;
		current().univariateClauses.push_back(*cit);
		cit = mUndecidedClauses.erase(cit);
	}
	SMTRAT_LOG_DEBUG("smtrat.sat.mc", "-> " << mUndecidedClauses);
	
	// Check undecided variables whether they became univariate
	SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Undecided Variables: " << mUndecidedVariables);
	for (auto vit = mUndecidedVariables.begin(); vit != mUndecidedVariables.end();) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Looking at " << *vit);
		std::size_t level = computeVariableLevel(*vit);
		if (level != mCurrentLevel) {
			vit++;
			continue;
		}
		SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Associating " << *vit << " with " << var);
		setVariableLevel(*vit, mCurrentLevel);
		current().univariateVariables.push_back(*vit);
		vit = mUndecidedVariables.erase(vit);
	}
	SMTRAT_LOG_DEBUG("smtrat.sat.mc", "-> " << mUndecidedVariables);
}

void MCSATMixin::removeLastLevel() {
	assert(!mTheoryStack.empty());
	assert(mCurrentLevel < mTheoryStack.size() - 1);
	for (auto c: mTheoryStack.back().univariateClauses) {
		mClauseLevelMap[c] = 0;
	}
	for (auto v: mTheoryStack.back().univariateVariables) {
		setVariableLevel(v, 0);
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
	SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Pushing new level with " << var);
	mVariables.assign(var);
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
	mVariables.unassign(current().variable);
	mCurrentLevel--;
}

std::size_t MCSATMixin::addVariable(Minisat::Var variable) {
	if (mGetter.isTheoryAbstraction(variable)) {
		mVariables.add(mGetter.reabstractVariable(variable));
	}
	std::size_t level = computeVariableLevel(variable);
	if (level == std::numeric_limits<std::size_t>::max()) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Adding " << variable << " to undecided");
		mUndecidedVariables.push_back(variable);
	} else {
		SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Adding " << variable << " on level " << level);
		setVariableLevel(variable, level);
		mTheoryStack[level].univariateVariables.push_back(variable);
	}
	return level;
}

void MCSATMixin::addClause(Minisat::CRef clause) {
	SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Adding " << clause);
	for (std::size_t level = 1; level < mTheoryStack.size(); level++) {
		SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Checking if " << clause << " is univariate in " << mTheoryStack[level].variable);
		if (isClauseUnivariate(clause, level)) {
			SMTRAT_LOG_DEBUG("smtrat.sat.mc", clause << " is univariate in " << mTheoryStack[level].variable);
			mTheoryStack[level].univariateClauses.push_back(clause);
			mClauseLevelMap.emplace(clause, level);
			return;
		}
	}
	SMTRAT_LOG_DEBUG("smtrat.sat.mc", clause << " was not found to be univariate, adding to undecided.");
	mTheoryStack[0].univariateClauses.push_back(clause);
	mClauseLevelMap.emplace(clause, 0);
}

void MCSATMixin::removeClause(Minisat::CRef clause) {
	auto it = mClauseLevelMap.find(clause);
	SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Erasing " << clause << " from level " << it->second);
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
		vars.erase(current().variable);
		
	}
	SMTRAT_LOG_TRACE("smtrat.sat.mc", "Checking if " << formula << " is univariate: " << vars.empty());
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
		SMTRAT_LOG_TRACE("smtrat.sat.mc", "Variable " << variable << " is not a theory abstraction, thus on level 0");
		return 0;
	}
	FormulaT f = mGetter.reabstractVariable(variable);
	carl::Variables vars;
	f.arithmeticVars(vars);
	if (vars.empty()) {
		SMTRAT_LOG_TRACE("smtrat.sat.mc", "Variable " << variable << " / " << f << " has no variable, thus on level 0");
		return 0;
	}
	for (std::size_t level = 1; level < mTheoryStack.size(); level++) {
		vars.erase(get(level).variable);
		if (vars.empty()) {
			SMTRAT_LOG_TRACE("smtrat.sat.mc", "Variable " << variable << " / " << f << " is univariate in " << get(level).variable);
			return level;
		}
	}
	SMTRAT_LOG_DEBUG("smtrat.sat.mc", "Variable " << variable << " is undecided.");
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
	for (const auto& level: mcm.mTheoryStack) {
		os << level.variable << " (" << level.decisionLiteral << ")";
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
	os << mcm.mCurrentModel << std::endl;
	return os;
}

}
}
