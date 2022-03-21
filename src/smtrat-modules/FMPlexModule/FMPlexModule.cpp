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
	FMPlexModule<Settings>::FMPlexModule(const ModuleInput* _formula, Conditionals& _foundAnswer, uint_fast64_t _varNumber, uint_fast64_t _constrNumber, Manager* _manager) :
	  Module(_formula, _foundAnswer, _manager), mVarNumber(_varNumber), mConstrNumber(_constrNumber){
		mFMPlexBranch = std::list<FmplexLvl>();
		mAllConstraints = std::list<std::shared_ptr<FormulaWithOrigins>>();
		mAllConstraints = std::list<std::shared_ptr<FormulaWithOrigins>>();
	}

	template<typename Settings>
	bool FMPlexModule<Settings>::addCore(ModuleInput::const_iterator formula) {
		// Only take linear LEQ constraints for now. Would rather have a THROW thing here but can't find macro for it
		assert(formula->formula().getType() == carl::CONSTRAINT);
		assert(formula->formula().constraint().relation() == carl::Relation::LEQ);
		assert(formula->formula().constraint().maxDegree() <= 1);
		auto formulaPtr = std::make_shared<FormulaWithOrigins>(*formula);
		mAllConstraints.push_back(formulaPtr);
		mNewConstraints.push_back(formulaPtr);
	}

	template<typename Settings>
	void FMPlexModule<Settings>::removeCore(ModuleInput::const_iterator formula) {
		// Inconvenient search bc we need to compare the actual formulas, not their shared ptrs (as remove() would)
		for (const auto& it : mAllConstraints){
			if (*it == *formula) {
				mAllConstraints.remove(it);
				break;
			}
		}
		for (const auto& it : mNewConstraints){
			if (*it == *formula) {
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
		std::list<ConstraintWithInfo> newConstr = convertNewFormulas();

		// Add to first lvl (create it if necessary)
		if(mFMPlexBranch.empty()) {
			mFMPlexBranch.push_back(FmplexLvl(std::move(newConstr)));
		} else {
			mFMPlexBranch.front().addNonUsed(std::move(newConstr));
		}

		auto currentIterator = mFMPlexBranch.front();
		auto statusCheckResult = currentIterator.trueFalseCheck();
		while (!statusCheckResult.first) {
			bool backtracked = false;
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
			auto sameBoundsToCombine = std::list<ConstraintWithInfo>();
			auto oppositeBoundsToCombine = std::list<ConstraintWithInfo>();
			currentIterator.sortNonUsedIntoSameAndOpposite(&sameBoundsToCombine, &oppositeBoundsToCombine);
			if(backtracked){
				// TODO Continue Here
			} else {
				// TODO Continue Here
			}

		}

		return SAT;

	}

	template<typename Settings>
	void FMPlexModule<Settings>::updateModel() const {
		// TODO Implement
	}

	template<typename Settings>
	std::list<typename FMPlexModule<Settings>::ConstraintWithInfo> FMPlexModule<Settings>::fmplexCombine(boost::optional<carl::Variable> var, FMPlexModule::ConstraintWithInfo eliminator, std::list<ConstraintWithInfo> sameBounds, std::list<ConstraintWithInfo> oppositeBounds, typename std::list<FMPlexModule<Settings>::FmplexLvl>::iterator currentLvl) {
		if (!var)  return std::list<typename FMPlexModule<Settings>::ConstraintWithInfo>();
		auto res = std::list<typename FMPlexModule<Settings>::ConstraintWithInfo>();
		for (auto it : *sameBounds) {
			res.push_back(combine(eliminator, *it, var.get(), true, currentLvl));
		}
		for (auto it : *oppositeBounds) {
			res.push_back(combine(eliminator, *it, var.get(), false, currentLvl));
		}
		return std::move(res);
	}

	template<typename Settings>
	typename FMPlexModule<Settings>::ConstraintWithInfo FMPlexModule<Settings>::combine(FMPlexModule::ConstraintWithInfo eliminator, FMPlexModule::ConstraintWithInfo eliminee, carl::Variable var, bool sameBound, typename std::list<FMPlexModule<Settings>::FmplexLvl>::iterator currentLvl) {
		// Get the two polynomials
		auto eliminatorPolynomial = eliminator.formula.constraint().lhs();
		auto elimineePolynomial = eliminee.formula.constraint().lhs();

		// Determine needed factor and conflict level of the new constraint
		typename std::list<FMPlexModule<Settings>::FmplexLvl>::iterator cl;
		auto factor = elimineePolynomial.lcoeff(var) / eliminatorPolynomial.lcoeff(var);
		assert(factor.isConstant());
		if (sameBound) {
			factor = factor * (-1);
			cl = currentLvl;
		} else if (std::distance(eliminator.conflictLevel, currentLvl) <= std::distance(eliminee.conflictLevel, currentLvl)){
			cl = eliminator.conflictLevel;
		} else {
			cl = eliminee.conflictLevel;
		}

		// Compute new constraint
		FormulaT newConstraint = FormulaT(eliminatorPolynomial * factor + elimineePolynomial, carl::Relation::LEQ);
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
	void FMPlexModule<Settings>::resetBelow(typename std::list<FMPlexModule<Settings>::FmplexLvl>::iterator lvl) {
		lvl++;
		// Lvl should not be the very last element as we have just backtracked when calling this
		assert(lvl!= mFMPlexBranch.end());
		mFMPlexBranch.erase(lvl, mFMPlexBranch.end());
	}

	template<typename Settings>
	std::list<typename FMPlexModule<Settings>::ConstraintWithInfo> FMPlexModule<Settings>::convertNewFormulas() {
		auto res = std::list<ConstraintWithInfo>();
		for (const auto& subformula : mNewConstraints){
			res.push_back(ConstraintWithInfo(subformula, mFMPlexBranch.end()));
		}
		mNewConstraints.clear();
		return std::move(res);
	}

	/*** Nested Class FMPlexLvl Function Implementations ***/
	template<typename Settings>
	FMPlexModule<Settings>::FmplexLvl::FmplexLvl(std::list<ConstraintWithInfo> notUsed) : notUsed(notUsed){
		chooseVarAndDirection();
	}

	template<typename Settings>
	void FMPlexModule<Settings>::FmplexLvl::chooseVarAndDirection() {
		// TODO implement choice of different heuristics here based on settings
		baseHeuristicVarDir();
	}

	template<typename Settings>
	void FMPlexModule<Settings>::FmplexLvl::baseHeuristicVarDir() {
		// TODO implement: choose variable and direction, then set according class attributes.
	}

	template<typename Settings>
	void FMPlexModule<Settings>::FmplexLvl::chooseNextConstraint() {
		// TODO implement choice of different heuristics here based on settings
		baseHeuristicNextConstraint();
	}

	template<typename Settings>
	void FMPlexModule<Settings>::FmplexLvl::baseHeuristicNextConstraint() {
		assert(!todoConstraints.empty());
		// TODO implement: choose variable and direction, then set according class attributes.
	}

	template<typename Settings>
	void FMPlexModule<Settings>::FmplexLvl::addNonUsed(std::list<ConstraintWithInfo> additionalConstr) {
		notUsed.splice(notUsed.end(), additionalConstr);
	}

	template<typename Settings>
	std::pair<bool, std::set<typename std::list<typename FMPlexModule<Settings>::ConstraintWithInfo>::iterator>> FMPlexModule<Settings>::FmplexLvl::trueFalseCheck() {
		auto res = std::set<typename std::list<typename FMPlexModule<Settings>::ConstraintWithInfo>::iterator>();
		auto toRemove = std::set<typename FMPlexModule<Settings>::ConstraintWithInfo>();
		for (auto constraint: notUsed) {
			auto lhs = *constraint.formula.constraint().lhs();
			if (lhs.isConstant()){
				// TODO QUESTION changes / additional cases needed here for constraints other than LEQ
				if (lhs.constantPart() <= __gmp_expr<mpq_t, mpq_t>(0)) { // TODO QUESTION does this constant initialization work?
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
	typename std::list<typename FMPlexModule<Settings>::FmplexLvl>::iterator FMPlexModule<Settings>::FmplexLvl::analyzeConflict(std::set<typename std::list<FMPlexModule<Settings>::ConstraintWithInfo>::iterator> conflictConstraints, std::list<FmplexLvl> branch) {
		auto backtrackIt = branch.end();
		for (auto cConstr : conflictConstraints) {
			bool posFound = false;
			bool negFound = false;
			for(auto devCoeff = cConstr.derivationCoefficients.begin(); devCoeff != cConstr.derivationCoefficients.begin() && (!posFound || !negFound); devCoeff++) {
				if (devCoeff->second > carl::MultivariatePolynomial<__gmp_expr<mpz_t, mpz_t>>(0)){ // TODO QUESTION does this constant initialization work?
					posFound = true;
				} else if (devCoeff->second < carl::MultivariatePolynomial<__gmp_expr<mpz_t, mpz_t>>(0)) { // TODO QUESTION does this constant initialization work?
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
	void FMPlexModule<Settings>::FmplexLvl::sortNonUsedIntoSameAndOpposite(std::list<ConstraintWithInfo>& sameBounds, std::list<ConstraintWithInfo>& oppositeBounds) {
		for (auto constr :  notUsed) {
			auto vars = constr.formula.variables();
			if (vars.find(currentEliminator) != vars.end()){
				auto coeff = constr.formula.constraint().lhs().lcoeff(currentEliminator);
				if (eliminateViaLB == (coeff < carl::MultivariatePolynomial<__gmp_expr<mpz_t, mpz_t>>(0))){ // TODO QUESTION does this constant initialization work?
					// Eliminator and Eliminee are the same kind of bound
					sameBounds.push_back(*constr);
				} else {
					// Eliminator and Eliminee are opposite kinds of bounds
					oppositeBounds.push_back(*constr);
				}
			}
		}
	}

	}