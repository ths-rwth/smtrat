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
FMPlexModule<Settings>::FMPlexModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager) : Module(_formula, _conditionals, _manager){
	mFMPlexBranch = FMPlexBranch();
	mAllConstraints = std::list<std::shared_ptr<SimpleConstraint>>();
	mAllConstraints = std::list<std::shared_ptr<SimpleConstraint>>();
	mModelFit = false;
	mModelFitUntilHere = mNewConstraints.end();
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
	// Convert mNewConstraints to ConstraintsWithInfo
	ConstraintList newConstr = convertNewFormulas();

	// Check current model
	if (!mModel.empty()) {
		mModelFit = true;
		for (auto c : newConstr) {
			auto checkConstr = substitute(c.constraint().lhs, mModel);
			if (!checkConstr.isTrivialTrue()) {
				mModelFit = false;
				break;
			}
		}
		if (mModelFit) {
			mModelFitUntilHere = mNewConstraints.end();
			mModelFitUntilHere--;
			return SAT; // TODO how to enable / disable incrementality here?
		} else {
			mNewConstraints.clear();
		}
	}

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
				mFMPlexBranch.clear();
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

	if(!Settings::incremental) {
		mFMPlexBranch.clear();
	}
	return SAT;

}

template<typename Settings>
void FMPlexModule<Settings>::updateModel() const {
	assert(!mFMPlexBranch.empty());
	if (mModelFit) {
		return;
	} else {
		mModel.clear();
		// For now, we can ignore variables that are implicitly eliminated for which we at this point have no assigned value in the model yet
		// because we will later simply set them to 0
		for (auto itr = mFMPlexBranch.rbegin(); itr != mFMPlexBranch.rend(); itr++) {
			carl::Variable var = itr->varToEliminate;
			if (itr->currentEliminator.has_value()){
				// Solve for varToEliminate.
				auto lhs = substitute(itr->constraint().lhs, mModel);
				Rational varValue = (Rational(-1) * lhs.constantPart()) / lhs.lcoeff(itr->varToEliminate);
				mModel.assign(var, varValue);
			} else if (itr->eliminateViaLB) {
				// We only have upper bounds and thus haven't actually chosen an eliminator.
				// So now we need to find the sub
				Rational sub;
				bool set = false;
				for (ConstraintWithInfo c : itr->oppositeDirectionConstraints) {
					auto lhs = substitute(itr->constraint().lhs, mModel);
					Rational bound = (Rational(-1) * lhs.constantPart()) / lhs.lcoeff(itr->varToEliminate);
					if (!set || bound < sub) {
						sub = bound;
						set = true;
					}
				}
				mModel.assign(var, sub);
			} else {
				// We only have lower bounds and thus haven't actually chosen an eliminator.
				// So now we need to find the glb
				Rational glb;
				bool set = false;
				for (ConstraintWithInfo c : itr->oppositeDirectionConstraints) {
					auto lhs = substitute(itr->constraint().lhs, mModel);
					Rational bound = (Rational(-1) * lhs.constantPart()) / lhs.lcoeff(itr->varToEliminate);
					if (!set || bound > glb) {
						glb = bound;
						set = true;
					}
				}
				mModel.assign(var, glb);
			}
		}
		// Set all remaining vars to 0 (it is important that this is 0!)
		auto vars = std::set<carl::Variable>();
		for (std::shared_ptr<SimpleConstraint> constraint : mAllConstraints) {
			carl::carlVariables newVars = carl::variables(constraint->lhs());
			vars.template insert(newVars.begin(), newVars.end());
		}
		for (carl::Variable var : vars) {
			if (!mModel.template contains(var)) mModel.template assign(var, Rational(0));
		}
	}




}

template<typename Settings>
typename FMPlexModule<Settings>::ConstraintList FMPlexModule<Settings>::fmplexCombine(boost::optional<carl::Variable> var, ConstraintWithInfo eliminator, ConstraintList sameBounds, ConstraintList oppositeBounds, BranchIterator currentLvl) {
	if (!var)  return ConstraintList();
	auto res = ConstraintList();
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
		factor = factor * Rational(-1);
		cl = currentLvl;
	} else if (std::distance(eliminator.conflictLevel, currentLvl) <= std::distance(eliminee.conflictLevel, currentLvl)){ // TODO handle here that upon constraint creation, cl value is branch.end()
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
	return std::move(res);
}

/*** Nested Class FMPlexLvl Function Implementations ***/
template<typename Settings>
FMPlexModule<Settings>::FmplexLvl::FmplexLvl(ConstraintList notUsed) : notUsed(notUsed){
	eliminateViaLB = true;
	chooseVarAndDirection();
}

template<typename Settings>
void FMPlexModule<Settings>::FmplexLvl::chooseVarAndDirection() {
	// Other heuristics may be added here (+ create option in settings)
	switch (Settings::variableDirectionHeuristic) {
		case "Simple":
			simpleHeuristicVarDir();
			break;
		default:
			baseHeuristicVarDir();
			break;
	}
}


template<typename Settings>
void FMPlexModule<Settings>::FmplexLvl::baseHeuristicVarDir() {
	// Set varToEliminate to next best var we can find
	carl::carlVariables occurringVars = carl::variables(notUsed.constraint.lhs());
	varToEliminate = *occurringVars.begin();
	eliminateViaLB = true;
}

template<typename Settings>
void FMPlexModule<Settings>::FmplexLvl::simpleHeuristicVarDir() {
	// first integer: number of upper bounds. second integer: number of lower bounds.
	auto varBoundCounter = std::map<carl::Variable, std::pair<uint_fast64_t, uint_fast64_t>>();
	for (auto it : notUsed) {
		carl::carlVariables occurringVars = carl::variables(notUsed.constraint.lhs());
		for (auto var : occurringVars) {
			if (varBoundCounter.find(var) == varBoundCounter.end()) {
				varBoundCounter[var] = std::make_pair(0,0);
			}
			assert (it.constraint.lhs().lcoeff(var) != Rational(0));
			if (it.constraint.lhs().lcoeff(var) > Rational(0)){
				varBoundCounter[var].first++;
			} else {
				varBoundCounter[var].second++;
			}
		}
	}
	std::pair<carl::Variable, std::pair<uint_fast64_t, uint_fast64_t>> bestVar = *varBoundCounter.begin();
	bool bestOneDir = bestVar.second.first * bestVar.second.second == 0;
	for (auto currentVar : varBoundCounter) {
		bool currentOneDir = currentVar.second.first * currentVar.second.second == 0;
		// This is all in one if to make use of the short-circuiting AND and OR operators, I know it's not very readable :')
		if ((!bestOneDir && currentOneDir) || (bestOneDir && currentOneDir && bestVar.second.first + bestVar.second.second < currentVar.second.first + currentVar.second.second) || (!bestOneDir && !currentOneDir && std::min(currentVar.second.first, currentVar.second.second) < std::min(bestVar.second.first, bestVar.second.second))){
			bestVar = currentVar;
			bestOneDir = currentOneDir;
		}
	}
	varToEliminate = bestVar.first;
	if (bestVar.second.first >= bestVar.second.second){
		eliminateViaLB = true;
	} else {
		eliminateViaLB = false;
	}
}

template<typename Settings>
void FMPlexModule<Settings>::FmplexLvl::chooseNextConstraint() {
	// Other heuristics may be added here (+ create option in settings)
	switch (Settings::constraintHeuristic) {
	case "Simple":
		simpleHeuristicNextConstraint();
		break;
	default:
		baseHeuristicNextConstraint();
		break;
	}
}

template<typename Settings>
void FMPlexModule<Settings>::FmplexLvl::baseHeuristicNextConstraint() {
	assert(!todoConstraints.empty());
	// Move to doneConstraints
	if (currentEliminator.has_value()) doneConstraints.push_back(currentEliminator.get());
	// Choose next best one
	currentEliminator = todoConstraints.front();
	todoConstraints.pop_front();
}

template<typename Settings>
void FMPlexModule<Settings>::FmplexLvl::simpleHeuristicNextConstraint() {
	assert(!todoConstraints.empty());
	// Move to doneConstraints
	if (currentEliminator.has_value()) doneConstraints.push_back(currentEliminator.get());
	// Chose one with fewest number of different original constriants in linear combination
	ConstraintWithInfo bestEliminator = todoConstraints.front();
	for (auto constr : todoConstraints) {
		if (constr.derivationCoefficients.size() < bestEliminator.derivationCoefficients.size()) {
			bestEliminator = constr;
		}
	}
	currentEliminator = bestEliminator;
	todoConstraints.remove(bestEliminator);

}

template<typename Settings>
void FMPlexModule<Settings>::FmplexLvl::addNonUsed(ConstraintList additionalConstr) {
	notUsed.splice(notUsed.end(), additionalConstr);
}

template<typename Settings>
std::pair<bool, std::set<typename FMPlexModule<Settings>::ConstraintList::iterator>> FMPlexModule<Settings>::FmplexLvl::trueFalseCheck() {
	auto res = std::set<typename ConstraintList::iterator>();
	auto toRemove = std::set<ConstraintWithInfo>();
	for (auto it: notUsed) {
		if (it->constraint.isTrivialTrue()){
			toRemove.push_back(*it);
		} else if (it->constraint.isTrivialFalse()){
			res.push_back(it);
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
		if (negFound && posFound) {
			// Local Conflict, apply chosen backtracking mode
			switch (Settings::backTrackingMode) {
				case "oneStep":
					backtrackIt = branch.find(this);
					backtrackIt--;
					break;
				case "furthest":
					if (std::distance(branch.begin(), backtrackIt) > std::distance(branch.begin(), cConstr->conflictLevel)){
							backtrackIt = cConstr->conflictLevel;
					}
					break;
				}
				// TODO possible third backtracking mode here?
		} else {
			// Global Conflict
			return branch.end();
		}
	}
	return backtrackIt;
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