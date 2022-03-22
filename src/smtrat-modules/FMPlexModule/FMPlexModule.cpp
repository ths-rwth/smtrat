/**
* @file FMPlexModule.cpp
* @author Svenja Stein <svenja.stein@rwth-aachen.de>
*
* @version 2022-03-15
* Created on 2022-03-15.
*/

#include "FMPlexModule.h"

namespace smtrat {

template<class Settings>
FMPlexModule<Settings>::FMPlexModule(const ModuleInput* _formula, Conditionals& _foundAnswer, Manager* _manager) : Module(_formula, _foundAnswer, _manager){
	mFMPlexBranch = FMPlexBranch();
	mAllConstraints = std::list<std::shared_ptr<SimpleConstraint>>();
	mAllConstraints = std::list<std::shared_ptr<SimpleConstraint>>();
}

template<typename Settings>
bool FMPlexModule<Settings>::addCore(ModuleInput::const_iterator formula) {
	// Only take linear LEQ constraints for now. Would rather have a THROW thing here but can't find macro for it
	assert(formula->formula().getType() == carl::CONSTRAINT);
	assert(formula->formula().constraint().relation() == carl::Relation::LEQ);
	assert(formula->formula().constraint().maxDegree() <= 1);
	auto formulaPtr = std::make_shared<SimpleConstraint>(formula->formula().constraint());
	mAllConstraints.push_back(formulaPtr);
	mNewConstraints.push_back(formulaPtr);
}

template<typename Settings>
void FMPlexModule<Settings>::removeCore(ModuleInput::const_iterator formula) {
	// Inconvenient search bc we need to compare the actual formulas, not their shared ptrs (as remove() would)
	auto constrToRemove = SimpleConstraint(formula->formula().constraint().lhs(), formula->formula().constraint().relation());
	for (const auto& it : mAllConstraints){
		if (*it == constrToRemove) {
			mAllConstraints.remove(it);
			break;
		}
	}
	for (const auto& it : mNewConstraints){
		if (*it == constrToRemove) {
			mNewConstraints.remove(it);
			return;
		}
	}
	mFMPlexBranch.clear();
}

template<typename Settings>
Answer FMPlexModule<Settings>::checkCore() {
	// TODO Check if current model (if available) satisfies the new additional constraints

	// Convert mNewConstraints to ConstraintsWithInfo
	ConstraintList newConstr = convertNewFormulas();

	// Add to first lvl (create it if necessary)
	if(mFMPlexBranch.empty()) {
		mFMPlexBranch.push_back(FmplexLvl(std::move(newConstr)));
	} else {
		mFMPlexBranch.front().addNonUsed(std::move(newConstr));
	}

	auto currentIterator = mFMPlexBranch.front();
	auto statusCheckResult = currentIterator.trueFalseCheck();
	bool backtracked = false;
	while (!statusCheckResult.first) {
		if(!statusCheckResult.second.empty()){
			// Conflict
			currentIterator = currentIterator->analyzeConflict(statusCheckResult.second, mFMPlexBranch);
			if (currentIterator == mFMPlexBranch.end()) {
				// Global Conflict, we are done
				return UNSAT;
			} else {
				// Local Conflict, we backtracked
				resetBelow(currentIterator);
				currentIterator->chooseNextConstraint();
				backtracked = true;
			}
		}
		// We are now on the right level + want to apply the next elimination
		// Sort constraints from notUsed into same + opposite combination lists
		auto sameBoundsToCombine = ConstraintList();
		auto oppositeBoundsToCombine = ConstraintList();
		if(backtracked){
			// If we backtracked, we need to recombine everything
			sameBoundsToCombine.insert(currentIterator->doneConstraints.begin(), currentIterator->doneConstraints.end());
			sameBoundsToCombine.insert(currentIterator->doneConstraints.begin(), currentIterator->doneConstraints.end());
			oppositeBoundsToCombine.insert(currentIterator->oppositeDirectionConstraints.begin(), currentIterator->oppositeDirectionConstraints.end());
			backtracked = false;
		}
		currentIterator.sortNonUsedIntoSameAndOpposite(&sameBoundsToCombine, &oppositeBoundsToCombine);
		if (!currentIterator.currentEliminator && !currentIterator.todoConstraints.empty()) {
			currentIterator.chooseNextConstraint();
		}

		if (std::next(currentIterator) == mFMPlexBranch.end()) {
			mFMPlexBranch.push_back(FmplexLvl(fmplexCombine(currentIterator.varToEliminate, currentIterator.currentEliminator, std::move(sameBoundsToCombine), std::move(oppositeBoundsToCombine))));
			currentIterator++;
		} else {
			currentIterator++;
			currentIterator.addNonUsed(fmplexCombine(currentIterator.varToEliminate, currentIterator.currentEliminator, std::move(sameBoundsToCombine), std::move(oppositeBoundsToCombine)));
		}
		statusCheckResult = currentIterator.trueFalseCheck();
	}

	return SAT;

}

template<typename Settings>
void FMPlexModule<Settings>::updateModel() const {
	// TODO Implement
	
}

template<typename Settings>
typename FMPlexModule<Settings>::ConstraintList FMPlexModule<Settings>::fmplexCombine(boost::optional<carl::Variable> var, ConstraintWithInfo eliminator, ConstraintList sameBounds, ConstraintList oppositeBounds, BranchIterator currentLvl) {
	if (!var)  return typename FMPlexModule<Settings>::ConstraintList();
	auto res = typename FMPlexModule<Settings>::ConstraintList();
	for (auto it : *sameBounds) {
		res.push_back(combine(eliminator, *it, var.get(), true, currentLvl));
	}
	for (auto it : *oppositeBounds) {
		res.push_back(combine(eliminator, *it, var.get(), false, currentLvl));
	}
	return std::move(res);
}

template<typename Settings>
typename FMPlexModule<Settings>::ConstraintWithInfo FMPlexModule<Settings>::combine(ConstraintWithInfo eliminator, ConstraintWithInfo eliminee, carl::Variable var, bool sameBound, BranchIterator currentLvl) {
	// Get the two polynomials
	Poly eliminatorPolynomial = eliminator.formula.constraint().lhs();
	Poly elimineePolynomial = eliminee.formula.constraint().lhs();

	// Determine needed factor and conflict level of the new constraint
	BranchIterator cl;
	Rational factor = elimineePolynomial.lcoeff(var).constantPart() / eliminatorPolynomial.lcoeff(var).constantPart();
	if (sameBound) {
		factor = factor * (-1);
		cl = currentLvl;
	} else if (std::distance(eliminator.conflictLevel, currentLvl) <= std::distance(eliminee.conflictLevel, currentLvl)){
		cl = eliminator.conflictLevel;
	} else {
		cl = eliminee.conflictLevel;
	}

	// Compute new constraint
	SimpleConstraint newConstraint = SimpleConstraint(eliminatorPolynomial * factor + elimineePolynomial, carl::Relation::LEQ);
	ConstraintWithInfo res = ConstraintWithInfo(std::move(newConstraint), std::move(cl));

	// Update Derivation coefficients: Coeffs in both or only eliminator
	for (auto it : eliminator.derivationCoefficients) {
		if (eliminee.derivationCoefficients.find(it->first) != eliminee.derivationCoefficients.end()) {
			res.derivationCoefficients[it.first] = factor * it.second + eliminee.derivationCoefficients[it.first];
		} else {
			res.derivationCoefficients[it.first] = factor * it.second;
		}
	}
	// Update Derivation coefficients: Coeffs only in eliminee
	for (auto it : eliminee.derivationCoefficients) {
		if (res.derivationCoefficients.find(it->first) == res.derivationCoefficients.end()) {
			res.derivationCoefficients[it.first] = eliminee.derivationCoefficients[it.first];
		}
	}

	return std::move(res);
}

template<typename Settings>
void FMPlexModule<Settings>::resetBelow(BranchIterator lvl) {
	lvl++;
	// Lvl should not be the very last element as we have just backtracked when calling this
	assert(lvl!= mFMPlexBranch.end());
	mFMPlexBranch.erase(lvl, mFMPlexBranch.end());
}

template<typename Settings>
typename FMPlexModule<Settings>::ConstraintList FMPlexModule<Settings>::convertNewFormulas() {
	ConstraintList res = ConstraintList();
	for (const auto& subformula : mNewConstraints){
		res.push_back(ConstraintWithInfo(subformula, mFMPlexBranch.end()));
	}
	mNewConstraints.clear();
	return std::move(res);
}

/*** Nested Class FMPlexLvl Function Implementations ***/
template<typename Settings>
FMPlexModule<Settings>::FmplexLvl::FmplexLvl(ConstraintList notUsed) : notUsed(notUsed){
	chooseVarAndDirection();
}

template<typename Settings>
void FMPlexModule<Settings>::FmplexLvl::chooseVarAndDirection() {
	// Other heuristics may be added here (+ create option in settings)
	switch (Settings::variableDirectionHeuristic) {
		case "Basic":
			baseHeuristicVarDir();
			break;
		default:
			baseHeuristicVarDir();
			break;
	}
}

template<typename Settings>
void FMPlexModule<Settings>::FmplexLvl::baseHeuristicVarDir() {
	// TODO implement: choose variable and direction, then set according class attributes.
}

template<typename Settings>
void FMPlexModule<Settings>::FmplexLvl::chooseNextConstraint() {
	// Other heuristics may be added here (+ create option in settings)
	switch (Settings::constraintHeuristic) {
	case "Basic":
		baseHeuristicNextConstraint();
		break;
	default:
		baseHeuristicNextConstraint();
		break;
	}
	baseHeuristicNextConstraint();
}

template<typename Settings>
void FMPlexModule<Settings>::FmplexLvl::baseHeuristicNextConstraint() {
	assert(!todoConstraints.empty());
	// TODO implement: choose variable and direction, then set according class attributes.
}

template<typename Settings>
void FMPlexModule<Settings>::FmplexLvl::addNonUsed(ConstraintList additionalConstr) {
	notUsed.splice(notUsed.end(), additionalConstr);
}

template<typename Settings>
std::pair<bool, std::set<typename FMPlexModule<Settings>::ConstraintList::iterator>> FMPlexModule<Settings>::FmplexLvl::trueFalseCheck() {
	auto res = std::set<typename ConstraintList::iterator>();
	auto toRemove = std::set<ConstraintWithInfo>();
	for (auto constraint: notUsed) {
		Poly lhs = constraint.constraint.lhs();
		if (lhs.isConstant()){
			// TODO QUESTION changes / additional cases needed here for constraints other than LEQ
			if (lhs.constantPart() <= Rational(0)) {
				// Trivially true
				toRemove.push_back(*constraint);
			} else {
				// Trivially false
				res.push_back(constraint);
			}
		}
	}
	for (auto r : toRemove) notUsed.remove(r);
	bool sat = notUsed.empty();
	assert(!sat || res.empty());
	return std::make_pair(sat, std::move(res));
}
template<typename Settings>
typename FMPlexModule<Settings>::BranchIterator FMPlexModule<Settings>::FmplexLvl::analyzeConflict(std::set<typename ConstraintList::iterator> conflictConstraints, FMPlexBranch branch) {
	BranchIterator backtrackIt = branch.end();
	for (auto cConstr : conflictConstraints) {
		bool posFound = false;
		bool negFound = false;
		for(auto devCoeff = cConstr.derivationCoefficients.begin(); devCoeff != cConstr.derivationCoefficients.begin() && (!posFound || !negFound); devCoeff++) {
			if (devCoeff->second > Rational(0)){
				posFound = true;
			} else if (devCoeff->second < Rational(0)) {
				negFound = true;
			}
		}
		if (negFound && posFound && std::distance(branch.begin(), backtrackIt) > std::distance(branch.begin(), cConstr->conflictLevel)) {
			// Local Conflict with further backtracking required
			backtrackIt = cConstr->conflictLevel;
		} else {
			// Global Conflict
			return branch.end();
		}
	}
}

template<typename Settings>
void FMPlexModule<Settings>::FmplexLvl::sortNonUsedIntoSameAndOpposite(ConstraintList& sameBounds, ConstraintList& oppositeBounds) {
	for (auto constr :  notUsed) {
		auto vars = constr.formula.variables();
		if (vars.find(currentEliminator) != vars.end()){
			Rational coeff = constr.formula.constraint().lhs().lcoeff(currentEliminator);
			if (eliminateViaLB == (coeff < Rational(0))){
				// Eliminator and Eliminee are the same kind of bound
				sameBounds.push_back(*constr);
				todoConstraints.push_back(*constr);
			} else {
				// Eliminator and Eliminee are opposite kinds of bounds
				oppositeBounds.push_back(*constr);
				oppositeDirectionConstraints.push_back(*constr);
			}
		}
	}
}

}