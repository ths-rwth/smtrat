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
	mAllConstraints = std::list<std::shared_ptr<BasicConstraint>>();
	mNewConstraints = std::list<std::shared_ptr<BasicConstraint>>();
	mModelFit = false;
	mModelFitUntilHere = mNewConstraints.end();
	counter = 1;
}

template<typename Settings>
bool FMPlexModule<Settings>::addCore(ModuleInput::const_iterator formula) {
	//assert(formula->formula().getType() == carl::CONSTRAINT);
	assert(formula->formula().constraint().maxDegree() <= 1);
	if (formula->formula().constraint().relation() == carl::Relation::LEQ) {
		auto formulaPtr = std::make_shared<BasicConstraint>(formula->formula().constraint().lhs(), carl::Relation::LEQ);
		mAllConstraints.push_back(formulaPtr);
		mNewConstraints.push_back(formulaPtr);
	} else if (formula->formula().constraint().relation() == carl::Relation::LESS) {
		auto formulaPtr = std::make_shared<BasicConstraint>(formula->formula().constraint().lhs(), carl::Relation::LESS);
		mAllConstraints.push_back(formulaPtr);
		mNewConstraints.push_back(formulaPtr);
	} else if (formula->formula().constraint().relation() == carl::Relation::EQ) {
		auto formulaPtr1 = std::make_shared<BasicConstraint>(formula->formula().constraint().lhs(), carl::Relation::LEQ);
		auto formulaPtr2 = std::make_shared<BasicConstraint>(Rational (-1) * formula->formula().constraint().lhs(), carl::Relation::LEQ);
		mAllConstraints.push_back(formulaPtr1);
		mNewConstraints.push_back(formulaPtr1);
		mAllConstraints.push_back(formulaPtr2);
		mNewConstraints.push_back(formulaPtr2);
	} else {
		//std::cout << "RELATION NOT SUPPORTED: " << formula->formula().constraint().relation() << std::endl;
		//std::cout << "LHS: " << formula->formula().constraint().lhs();
		assert(false);
		SMTRAT_STATISTICS_CALL(stats.unsupprelation());
		std::exit(44);
	}
	return true;
}

template<typename Settings>
void FMPlexModule<Settings>::removeCore(ModuleInput::const_iterator formula) {
	if (formula->formula().constraint().relation() != carl::Relation::EQ) {
		// Inconvenient search bc we need to compare the actual formulas, not their shared ptrs (as remove() would)
		auto constrToRemove = BasicConstraint(formula->formula().constraint().lhs(), formula->formula().constraint().relation());
		bool found = false;
		std::shared_ptr<BasicConstraint> toRemove;
		for (const auto& it : mAllConstraints) {
			if (it->lhs() == constrToRemove.lhs() && it->relation() == constrToRemove.relation()) {
				toRemove = it;
				found = true;
				break;
			}
		}
		mAllConstraints.remove(toRemove);
		mNewConstraints.remove(toRemove);
		assert(found);
		resetBranch();
	} else {
		// Special Treatment for equalities
		auto constrToRemove1 = BasicConstraint(formula->formula().constraint().lhs(), carl::Relation::LEQ);
		auto constrToRemove2 = BasicConstraint(Rational (-1) * formula->formula().constraint().lhs(), carl::Relation::LEQ);
		std::shared_ptr<BasicConstraint> toRemove1;
		std::shared_ptr<BasicConstraint> toRemove2;
		bool found1 = false;
		bool found2 = false;
		for (const auto& it : mAllConstraints) {
			if (it->relation() == carl::Relation::LEQ) {
				if (it->lhs() == constrToRemove1.lhs()) {
					toRemove1 = it;
					found1 = true;
				} else if (it->lhs() == constrToRemove2.lhs()) {
					toRemove2 = it;
					found2 = true;
				}
				if (found1 && found2) break;
			}

		}
		assert(found1 && found2);
		mAllConstraints.remove(toRemove1);
		mAllConstraints.remove(toRemove2);

		mModel.clear();

		found1 = false;
		found2 = false;
		for (const auto& it : mNewConstraints) {
			if (it->relation() == carl::Relation::LEQ) {
				if (it->lhs() == constrToRemove1.lhs()) {
					toRemove1 = it;
					found1 = true;
				} else if (it->lhs() == constrToRemove2.lhs()) {
					toRemove2 = it;
					found2 = true;
				}
				if (found1 && found2) break;
			}

		}
		assert(found1 == found2);
		resetBranch();
	}
}

template<typename Settings>
Answer FMPlexModule<Settings>::checkCore() {
	SMTRAT_STATISTICS_CALL(stats.countCheckSatCalls());
	//SMTRAT_VALIDATION_ADD("fmplex", std::string("checkCoreCall"), (FormulaT)*mpReceivedFormula, true);
	//std::cout << "Call " << counter << "\n";
	//std::cout << "Formula: " << FormulaT(*mpReceivedFormula) << "\n";
	counter++;
	if (!Settings::incremental) {
		mModel.clear();
		resetBranch();
	}
	// Check current model
	if (!mModel.empty()) {
		mModelFit = true;
		for (auto c = mModelFitUntilHere == mNewConstraints.end() ? mNewConstraints.begin() : mModelFitUntilHere; c != mNewConstraints.end() && mModelFit; c++) {
			auto checkConstr = c->get()->lhs();


			/*std::cout << "replace in: ";
			for (auto t : checkConstr) {
				std::cout << t << " + ";
			}
			std::cout << "\n";
			for (auto modelValuation : mModel){
				std::cout << "var: " << modelValuation.first.asVariable().name() << ", value: " << modelValuation.second.asRational() << "\n";
				// if statement is quickfix for now. there are terms in some multivariate polynomials that evaluate to 0 but have not been removed for some reason
				if (checkConstr.lcoeff(modelValuation.first.asVariable()) != 0){
					substitute_inplace(checkConstr, modelValuation.first.asVariable(), Poly(modelValuation.second.asRational()));
				}
				substitute_inplace(checkConstr, modelValuation.first.asVariable(), Poly(modelValuation.second.asRational()));

			}*/
			carl::carlVariables vars = carl::variables(checkConstr);
			for (auto var : vars) {
				if (mModel.find(var) == mModel.end()) {
					mModelFit = false;
					break;
				} else if (checkConstr.lcoeff(var) != 0) {
					substitute_inplace(checkConstr, var, Poly(mModel.find(var)->second.asRational()));
				}
			}
			if (!BasicConstraint(checkConstr, c->get()->relation()).is_trivial_true()) {
				mModelFit = false;
			}
		}
		if (mModelFit) {
			mModelFitUntilHere = mNewConstraints.end();
			mModelFitUntilHere--;
			SMTRAT_LOG_INFO("fmplex", "Model Fits SAT");
			//std::cout << "SAT \n";
			return SAT;
		} else {
			mModelFitUntilHere = mNewConstraints.end();
		}
	}
	// Convert mNewConstraints to ConstraintsWithInfo
	ConstraintList newConstr = convertNewFormulas();
	// Add to first lvl (create it if necessary)
	if(mFMPlexBranch.empty()) {
		mFMPlexBranch.push_back(FmplexLvl(newConstr));
		mFMPlexBranch.front().chooseVarAndDirection();
	} else {
		mFMPlexBranch.front().connector.insert(mFMPlexBranch.front().connector.end(), newConstr.begin(), newConstr.end());
	}
	// Preparations for main loop
	BranchIterator currentIterator = mFMPlexBranch.begin();
	auto statusCheckResult = currentIterator->trueFalseCheck();
	// statusCheckResult (true, empty) -> SAT
	// statusCheckResult (false, empty) -> don't know yet
	// statusCheckResult (false, !empty) -> conflict
	bool redoCombinations = false;
	while (!statusCheckResult.first) {
		assert(!(statusCheckResult.first && !statusCheckResult.second.empty()));
		if(!statusCheckResult.second.empty()){
			// Conflict
			BranchIterator backtrackResult = currentIterator->analyzeConflict(statusCheckResult.second, &mFMPlexBranch, currentIterator);
			if (backtrackResult == mFMPlexBranch.end()) {
				// Global Conflict, we are done
				SMTRAT_STATISTICS_CALL(stats.countGConflicts());
				generateTrivialInfeasibleSubset();
				resetBranch();
				mModel.clear();
				mModelFit = false;
				mModelFitUntilHere = mNewConstraints.end();
				//std::cout << "UNSAT \n";
				return UNSAT;
			} else {
				// Local Conflict
				SMTRAT_STATISTICS_CALL(stats.countLConflicts());
				currentIterator = backtrackResult;
				resetBelow(currentIterator);
				/*if (currentIterator->todoConstraints.empty()) {
					std::cout << "\nProblematic backtrack level reached.\n";
					std::cout << "\nVariable to eliminate: " << currentIterator->varToEliminate.get().name() << "\n";
					if (currentIterator->eliminateViaLB) std::cout << "\nEliminating via lower bound.\n";
					else std::cout << "\nEliminating via upper bound.\n";
					std::cout << "\nCurrentEliminator: " << currentIterator->currentEliminator.get().constraint << "\n";
					std::cout << "\ndoneConstraints:\n";
					for (auto c : currentIterator->doneConstraints) {
						std::cout << c.constraint << "\n";
					}
					std::cout << "\noppositeConstraints:\n";
					for (auto c : currentIterator->oppositeDirectionConstraints) {
						std::cout << c.constraint << "\n";
					}
					std::cout << "\nnon-bounds:\n";
					for (auto c : currentIterator->nonBoundConstraints) {
						std::cout << c.constraint << "\n";
					}
				}*/
				assert(!currentIterator->todoConstraints.empty());
				currentIterator->chooseNextConstraint();
				redoCombinations = true;
			}
		}

		//std::cout << "\nOn level " << std::distance(mFMPlexBranch.begin(), currentIterator) << "\n";
		//if (currentIterator->varToEliminate) std::cout << "variable: " << currentIterator->varToEliminate.get().name();
		// We are now on the right level + want to apply the next elimination
		// Sort constraints from connector into same + opposite combination lists + the level's lists as well
		auto sameBoundsToCombine = ConstraintList();
		auto oppositeBoundsToCombine = ConstraintList();
		currentIterator->sortConnectorIntoSameOppositeNone(sameBoundsToCombine, oppositeBoundsToCombine);

		// If we have not chosen an eliminator yet but now have choices available
		if (!currentIterator->currentEliminator.has_value() && !currentIterator->todoConstraints.empty()) {
			currentIterator->chooseNextConstraint();
			redoCombinations = true;
		}

		// If we have to combine everything on the level again because there is a new eliminator
		if(redoCombinations){
			sameBoundsToCombine.clear();
			oppositeBoundsToCombine.clear();
			currentIterator->connector.clear();

			sameBoundsToCombine.insert(sameBoundsToCombine.end(), currentIterator->doneConstraints.begin(), currentIterator->doneConstraints.end());
			sameBoundsToCombine.insert(sameBoundsToCombine.end(), currentIterator->todoConstraints.begin(), currentIterator->todoConstraints.end());
			oppositeBoundsToCombine.insert(oppositeBoundsToCombine.end(), currentIterator->oppositeDirectionConstraints.begin(), currentIterator->oppositeDirectionConstraints.end());
			currentIterator->connector.insert(currentIterator->connector.end(), currentIterator->nonBoundConstraints.begin(), currentIterator->nonBoundConstraints.end());

			redoCombinations = false;
		}

		assert(currentIterator->varToEliminate.is_initialized());
		assert(currentIterator->varToEliminate.has_value());

		ConstraintList combinationResult = fmplexCombine(currentIterator->varToEliminate, currentIterator->currentEliminator, std::move(sameBoundsToCombine), std::move(oppositeBoundsToCombine), currentIterator);
		SMTRAT_STATISTICS_CALL(stats.countGeneratedConstraints(combinationResult.size()));
		if (std::next(currentIterator) == mFMPlexBranch.end()) {
			mFMPlexBranch.push_back(FmplexLvl(combinationResult));
			transferBetweenConnectors(currentIterator);
			currentIterator++;
			currentIterator->chooseVarAndDirection();
		} else {
			transferBetweenConnectors(currentIterator);
			currentIterator++;
			currentIterator->connector.insert(currentIterator->connector.end(), combinationResult.begin(), combinationResult.end());
			if (!currentIterator->varToEliminate.has_value()){
				currentIterator->chooseVarAndDirection();
			}
		}

		statusCheckResult = currentIterator->trueFalseCheck();
	}
	SMTRAT_LOG_INFO("fmplex", "SAT");
	//std::cout << "SAT \n";
	return SAT;

}

template<typename Settings>
void FMPlexModule<Settings>::updateModel() const {
	if (mModelFit) {
		return;
	} else {
		assert(!mFMPlexBranch.empty());
		mModel.clear();
		// Set all vars to 0 (it is important that this is 0!)
		// This is so the implcitly eliminated vars are 0 already
		for (std::shared_ptr<BasicConstraint> constraint : mAllConstraints) {
			carl::carlVariables newVars = carl::variables(constraint->lhs());
			for (carl::Variable var : newVars) {
				mModel.assign(var, Rational(0));
			}
		}
		auto itr = mFMPlexBranch.rbegin();
		itr++;
		for (; itr != mFMPlexBranch.rend(); itr++) {
			assert(itr->varToEliminate.has_value());
			assert(itr->varToEliminate.is_initialized());
			carl::Variable var = itr->varToEliminate.get();
			if (itr->currentEliminator.has_value()){
				if (itr->currentEliminator->constraint.relation() == carl::Relation::LEQ){
					// We can put it on the bound
					auto lhs = itr->currentEliminator->constraint.lhs();
					for (auto modelValuation : mModel){
						if (modelValuation.first.asVariable() != itr->varToEliminate.get()){
							substitute_inplace(lhs, modelValuation.first.asVariable(), Poly(modelValuation.second.asRational()));
						}
					}
					Rational varValue = (Rational(-1) * lhs.constantPart()) / lhs.lcoeff(itr->varToEliminate.get()).constantPart();
					mModel.assign(var, varValue);
				} else {
					// We cannot put it on the bound as the inequality is strict
					if (itr->eliminateViaLB) {
						auto glbLhs = itr->currentEliminator->constraint.lhs();
						for (auto modelValuation : mModel){
							if (modelValuation.first.asVariable() != itr->varToEliminate.get()){
								substitute_inplace(glbLhs, modelValuation.first.asVariable(), Poly(modelValuation.second.asRational()));
							}

						}
						Rational glb = (Rational(-1) * glbLhs.constantPart()) / glbLhs.lcoeff(itr->varToEliminate.get()).constantPart();
						// So now we need to find the sub
						Rational sub;
						bool set = false;
						for (ConstraintWithInfo c : itr->oppositeDirectionConstraints) {
							auto lhs = c.constraint.lhs();
							for (auto modelValuation : mModel){
								if (modelValuation.first.asVariable() != itr->varToEliminate.get()){
									substitute_inplace(lhs, modelValuation.first.asVariable(), Poly(modelValuation.second.asRational()));
								}
							}
							Rational bound = (Rational(-1) * lhs.constantPart()) / lhs.lcoeff(itr->varToEliminate.get()).constantPart();
							if (!set || bound < sub) {
								sub = bound;
								set = true;
							}
						}
						if (itr->oppositeDirectionConstraints.empty()) mModel.assign(var, (glb + Rational(1)));
						else mModel.assign(var, (glb + sub)/2);
					} else {
						auto subLhs = itr->currentEliminator->constraint.lhs();
						for (auto modelValuation : mModel){
							if (modelValuation.first.asVariable() != itr->varToEliminate.get()){
								substitute_inplace(subLhs, modelValuation.first.asVariable(), Poly(modelValuation.second.asRational()));
							}
						}
						Rational sub = (Rational(-1) * subLhs.constantPart()) / subLhs.lcoeff(itr->varToEliminate.get()).constantPart();
						// So now we need to find the glb
						Rational glb;
						bool set = false;
						for (ConstraintWithInfo c : itr->oppositeDirectionConstraints) {
							auto lhs = c.constraint.lhs();
							for (auto modelValuation : mModel){
								if (modelValuation.first.asVariable() != itr->varToEliminate.get()){
									substitute_inplace(lhs, modelValuation.first.asVariable(), Poly(modelValuation.second.asRational()));
								}

							}
							Rational bound = (Rational(-1) * lhs.constantPart()) / lhs.lcoeff(itr->varToEliminate.get()).constantPart();
							if (!set || bound > glb) {
								glb = bound;
								set = true;
							}
						}
						// put value between sub and glb
						if (itr->oppositeDirectionConstraints.empty()) mModel.assign(var, (sub - Rational(1)));
						else mModel.assign(var, (sub + glb)/2);
					}
				}
			} else {
				if (itr->eliminateViaLB) {
					// We only have upper bounds and thus haven't actually chosen an eliminator.
					// So now we need to find the sub
					Rational sub;
					bool set = false;
					for (ConstraintWithInfo c : itr->oppositeDirectionConstraints) {
						auto lhs = c.constraint.lhs();
						for (auto modelValuation : mModel){
							if (modelValuation.first.asVariable() != itr->varToEliminate.get()){
								substitute_inplace(lhs, modelValuation.first.asVariable(), Poly(modelValuation.second.asRational()));
							}
						}
						Rational bound = (Rational(-1) * lhs.constantPart()) / lhs.lcoeff(itr->varToEliminate.get()).constantPart();
						// subtract 1 in case it's a strict bound
						if (c.constraint.relation() == carl::Relation::LESS) bound = bound - Rational(1);
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
						auto lhs = c.constraint.lhs();
						for (auto modelValuation : mModel){
							if (modelValuation.first.asVariable() != itr->varToEliminate.get()){
								substitute_inplace(lhs, modelValuation.first.asVariable(), Poly(modelValuation.second.asRational()));
							}
						}
						Rational bound = (Rational(-1) * lhs.constantPart()) / lhs.lcoeff(itr->varToEliminate.get()).constantPart();
						// add 1 in case it's a strict bound
						if (c.constraint.relation() == carl::Relation::LESS) bound = bound + Rational(1);
						if (!set || bound > glb) {
							glb = bound;
							set = true;
						}
					}
					mModel.assign(var, glb);
				}
			}
		}

	}





}

template<typename Settings>
typename FMPlexModule<Settings>::ConstraintList FMPlexModule<Settings>::fmplexCombine(boost::optional<carl::Variable> var, boost::optional<ConstraintWithInfo> eliminator, ConstraintList sameBounds, ConstraintList oppositeBounds, BranchIterator currentLvl) {
	if (!eliminator.has_value()){
		//std::cout << "Only bounds in one direction.\n";
		return ConstraintList();
	}

	auto res = ConstraintList();

	// Same-Bound Combinations
	for (auto it : sameBounds) {
		//std::cout << "Same-Bound combination.\n";
		res.push_back(combine(eliminator.get(), it, var.get(), true, currentLvl));
	}

	// Upper-Lower Combinations
	for (auto it : oppositeBounds) {
		//std::cout << "Upper-Lower combination.\n";
		res.push_back(combine(eliminator.get(), it, var.get(), false, currentLvl));
	}
	return res;
}

template<typename Settings>
typename FMPlexModule<Settings>::ConstraintWithInfo FMPlexModule<Settings>::combine(ConstraintWithInfo eliminator, ConstraintWithInfo eliminee, carl::Variable var, bool sameBound, BranchIterator currentLvl) {
	// Get the two polynomials
	Poly eliminatorPolynomial = eliminator.constraint.lhs();
	Poly elimineePolynomial = eliminee.constraint.lhs();

	// Determine needed factor, conflict level and relation of the new constraint
	BranchIterator cl;
	Rational factor = abs(elimineePolynomial.lcoeff(var).constantPart()) / abs(eliminatorPolynomial.lcoeff(var).constantPart());
	carl::Relation rel;
	if (sameBound) {
		// Factor has to be negative
		factor = factor * Rational(-1);
		// Conflict level is the current level
		cl = currentLvl;
		// Relation
		if (eliminator.constraint.relation() == carl::Relation::LEQ && eliminee.constraint.relation() == carl::Relation::LESS){
			rel = carl::Relation::LESS;
		} else{
			rel = carl::Relation::LEQ;
		}
	} else {
		// Factor remains positive
		// Special handling in case any of the parents' CLs is branch.end() so that std::distance has no undefined behavior
		if (std::string("furthest").compare(Settings::backtrackingMode) == 0) {
			if (eliminator.conflictLevel == mFMPlexBranch.end()) {
				cl = eliminee.conflictLevel;
			} else if (eliminee.conflictLevel == mFMPlexBranch.end()) {
				cl = eliminator.conflictLevel;
			} else if (std::distance(eliminator.conflictLevel, currentLvl) <= std::distance(eliminee.conflictLevel, currentLvl)) {
				cl = eliminator.conflictLevel;
			} else {
				cl = eliminee.conflictLevel;
			}
		}
		// Relation: strict is dominant
		if (eliminator.constraint.relation() == carl::Relation::LEQ && eliminee.constraint.relation() == carl::Relation::LEQ){
			rel = carl::Relation::LEQ;
		} else {
			rel = carl::Relation::LESS;
		}
	}

	// Create new constraint
	BasicConstraint newConstraint = BasicConstraint((eliminatorPolynomial * factor + elimineePolynomial), rel);
	ConstraintWithInfo res = ConstraintWithInfo(newConstraint, cl);

	// Update Derivation coefficients: Coeffs in both or only eliminator
	for (auto it : eliminator.derivationCoefficients) {
		if (eliminee.derivationCoefficients.find(it.first) != eliminee.derivationCoefficients.end()) {
			res.derivationCoefficients[it.first] = factor * it.second + eliminee.derivationCoefficients[it.first];
		} else {
			res.derivationCoefficients[it.first] = factor * it.second;
		}
	}
	// Update Derivation coefficients: Coeffs only in eliminee
	for (auto it : eliminee.derivationCoefficients) {
		if (res.derivationCoefficients.find(it.first) == res.derivationCoefficients.end()) {
			res.derivationCoefficients[it.first] = eliminee.derivationCoefficients[it.first];
		}
	}
	return res;
}

template<typename Settings>
void FMPlexModule<Settings>::resetBelow(BranchIterator lvl) {
	auto nextLvl = BranchIterator(lvl);
	nextLvl++;
	// Lvl should not be the very last element as we have just backtracked when calling this
	assert(nextLvl!= mFMPlexBranch.end());
	mFMPlexBranch.erase(nextLvl, mFMPlexBranch.end());
}

template<typename Settings>
typename FMPlexModule<Settings>::ConstraintList FMPlexModule<Settings>::convertNewFormulas() {
	ConstraintList res = ConstraintList();
	for (const auto& subformula : mNewConstraints){
		res.push_back(ConstraintWithInfo(subformula, mFMPlexBranch.end()));
	}
	return res;
}

template<typename Settings>
void FMPlexModule<Settings>::transferBetweenConnectors(BranchIterator currentLvl) {
	auto nextLvl = BranchIterator(currentLvl);
	nextLvl++;
	nextLvl->connector.insert(nextLvl->connector.end(), currentLvl->connector.begin(), currentLvl->connector.end());
	currentLvl->connector.clear();
}

template<typename Settings>
void FMPlexModule<Settings>::resetBranch() {
	mFMPlexBranch.clear();
	mNewConstraints.clear();
	for (auto it : mAllConstraints){
		mNewConstraints.push_back(it);
	}
}

/*** Nested Class FMPlexLvl Function Implementations ***/
template<typename Settings>
FMPlexModule<Settings>::FmplexLvl::FmplexLvl(ConstraintList newConstraints) : connector(newConstraints){
	eliminateViaLB = true;
	varToEliminate = boost::none;
	todoConstraints = ConstraintList();
	doneConstraints = ConstraintList();
	oppositeDirectionConstraints = ConstraintList();
	nonBoundConstraints = ConstraintList();
}

template<typename Settings>
void FMPlexModule<Settings>::FmplexLvl::chooseVarAndDirection() {
	// Other heuristics may be added here (+ create option in settings)
	if (connector.empty()) {
		return;
	}
	if (std::string("Simple").compare(Settings::variableDirectionHeuristic) == 0) {
		simpleHeuristicVarDir();
	} else {
		baseHeuristicVarDir();
	}
}


template<typename Settings>
void FMPlexModule<Settings>::FmplexLvl::baseHeuristicVarDir() {
	// Set varToEliminate to next best var we can find
	carl::carlVariables occurringVars = carl::variables(connector.front().constraint.lhs());
	varToEliminate = *occurringVars.begin();
	if (connector.front().constraint.lhs().lcoeff(varToEliminate.get()) > Rational(0)) eliminateViaLB = false;
	else eliminateViaLB = true;
}

template<typename Settings>
void FMPlexModule<Settings>::FmplexLvl::simpleHeuristicVarDir() {
	// first integer: number of upper bounds. second integer: number of lower bounds.
	auto varBoundCounter = std::map<carl::Variable, std::pair<uint_fast64_t, uint_fast64_t>>();
	for (auto it : connector) {
		carl::carlVariables occurringVars = carl::variables(it.constraint.lhs());
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
	if (varBoundCounter.size() == 0) return;
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
	if (std::string("Simple").compare(Settings::constraintHeuristic) == 0) {
		simpleHeuristicNextConstraint();
	} else {
		baseHeuristicNextConstraint();
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
std::pair<bool, std::list<typename FMPlexModule<Settings>::ConstraintList::iterator>> FMPlexModule<Settings>::FmplexLvl::trueFalseCheck() {
	auto res = std::list<typename ConstraintList::iterator>();
	auto toRemove = std::list<ConstraintWithInfo>();
	for (auto it = connector.begin(); it != connector.end(); it++) {
		if (it->constraint.is_trivial_true()){
			toRemove.push_back(*it);
		} else if (it->constraint.is_trivial_false()){
			res.push_back(it);
		}
	}
	for (auto r : toRemove)
		connector.remove(r);
	bool sat = connector.empty();
	assert(!sat || res.empty());
	return std::make_pair(sat, std::move(res));
}
template<typename Settings>
typename FMPlexModule<Settings>::BranchIterator FMPlexModule<Settings>::FmplexLvl::analyzeConflict(std::list<typename ConstraintList::iterator> conflictConstraints, FMPlexBranch* branch, BranchIterator currentLvl) {
	BranchIterator backtrackIt = branch->end();
	for (auto cConstr : conflictConstraints) {
		//The following is for debugging purposes
		/*Poly sum = Poly(Rational(0));
		for (auto devCoeff : cConstr->derivationCoefficients) {
			sum = sum + Rational(devCoeff.second) * devCoeff.first.get()->lhs();
			//std::cout << "og constraint (" << devCoeff.first.get()->lhs()  << devCoeff.first.get()->relation() << "0 ) * " << Rational(devCoeff.second) << "\n";
		}
		assert(cConstr->constraint.lhs().constantPart() == sum.constantPart());*/

		bool posFound = false;
		bool negFound = false;
		for (auto devCoeff = cConstr->derivationCoefficients.begin(); devCoeff != cConstr->derivationCoefficients.end(); devCoeff++) {
			if (devCoeff->second > Rational(0)){
				posFound = true;
			} else if (devCoeff->second < Rational(0)) {
				negFound = true;
			}
		}
		if (negFound && posFound) {
			// Local Conflict, apply chosen backtracking mode
			assert (cConstr->conflictLevel != branch->end());
			if (std::string("oneStep").compare(Settings::backtrackingMode) == 0) {
				backtrackIt = currentLvl;
				while (backtrackIt->todoConstraints.empty() && backtrackIt != branch->begin()){
					backtrackIt--;
				}
				if (backtrackIt->todoConstraints.empty() && backtrackIt == branch->begin()) return branch->end();
				break;
			} else if (std::string("furthest").compare(Settings::backtrackingMode) == 0 && std::distance(branch->begin(), backtrackIt) > std::distance(branch->begin(), cConstr->conflictLevel)){
				backtrackIt = cConstr->conflictLevel;
				while (backtrackIt->todoConstraints.empty() && backtrackIt != branch->begin()){
					backtrackIt--;
				}
				if (backtrackIt->todoConstraints.empty() && backtrackIt == branch->begin()) {
					return branch->end();
				}

			}
		} else {
			// Global Conflict
			return branch->end();
		}
	}
	return backtrackIt;
}

template<typename Settings>
void FMPlexModule<Settings>::FmplexLvl::sortConnectorIntoSameOppositeNone(ConstraintList& sameBounds, ConstraintList& oppositeBounds) {
	if (connector.empty()) return;
	assert(varToEliminate.has_value());
	ConstraintList toRemove = ConstraintList();
	for (typename ConstraintList::iterator c = connector.begin(); c != connector.end(); c++) {
		auto vars = carl::variables(c->constraint.lhs());
		if (std::find(vars.begin(), vars.end(), varToEliminate.get()) != vars.end()){
			Rational coeff = c->constraint.lhs().lcoeff(varToEliminate.get()).constantPart();
			if (eliminateViaLB == (coeff < Rational(0))){
				// Eliminator and Eliminee are the same kind of bound
				sameBounds.push_back(*c);
				todoConstraints.push_back(*c);
			} else {
				// Eliminator and Eliminee are opposite kinds of bounds
				oppositeBounds.push_back(*c);
				oppositeDirectionConstraints.push_back(*c);
			}
			toRemove.push_back(*c);
		} else {
			nonBoundConstraints.push_back(*c);
		}
	}
	for (auto c: toRemove){
		connector.remove(c);
	}
}

}
#include "Instantiation.h"