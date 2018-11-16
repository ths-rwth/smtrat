/**
 * @file CADModule.cpp
 *
 * @author Ulrich Loup
 * @since 2012-01-19
 * @version 2013-07-10
 */

#include "CADModule.h"

#include <memory>
#include <iostream>

#include <carl/core/logging.h>

#include "MISGeneration.h"
#include "SplitVariableSelector.h"

using carl::UnivariatePolynomial;
using carl::cad::EliminationSet;
using carl::cad::Constraint;
using carl::Polynomial;
using carl::CAD;
using carl::RealAlgebraicPoint;
using carl::cad::ConflictGraph;

using namespace std;

namespace smtrat
{

	template<typename Settings>
	CADModule<Settings>::CADModule(const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* const _manager):
		Module(_formula, _conditionals, _manager),
		mCAD(_conditionals),
		mConstraints(),
		hasFalse(false),
		mSubformulaQueue(),
		mConstraintsMap(),
		mRealAlgebraicSolution(),
		mConflictGraph(),
		mVariableBounds()
#ifdef SMTRAT_DEVOPTION_Statistics
		,mStats(new CADStatistics())
#endif
	{
		mInfeasibleSubsets.clear();	// initially everything is satisfied
		// CAD setting
		carl::cad::CADSettings setting = mCAD.getSetting();
		// general setting set
		setting = carl::cad::CADSettings::getSettings(carl::cad::CADSettingsType::BOUNDED); // standard
		setting.simplifyByFactorization = true;
		setting.simplifyByRootcounting  = true;
		setting.splitInteger = false;
		setting.integerHandling = Settings::integerHandling;
		setting.ignoreRoots = Settings::ignoreRoots;
		setting.computeConflictGraph = Settings::computeConflictGraph;

//		setting.autoSeparateEquations = false; // <- @TODO: find a correct implementation of the MIS for the only-strict or only-equations optimizations

		mCAD.alterSetting(setting);

		SMTRAT_LOG_TRACE("smtrat.cad", "Initial CAD setting:" << std::endl << setting);
	}

	template<typename Settings>
	CADModule<Settings>::~CADModule(){}

	/**
	 * This method just adds the respective constraint of the subformula, which ought to be one real constraint,
	 * to the local list of constraints. Moreover, the list of all variables is updated accordingly.
	 *
	 * Note that the CAD object is not touched here, the respective calls to CAD::addPolynomial and CAD::check happen in isConsistent.
	 * @param _subformula
	 * @return returns false if the current list of constraints was already found to be unsatisfiable (in this case, nothing is done), returns true previous result if the constraint was already checked for consistency before, otherwise true
	 */
	template<typename Settings>
	bool CADModule<Settings>::addCore(ModuleInput::const_iterator _subformula)
	{
		SMTRAT_LOG_FUNC("smtrat.cad", _subformula->formula());
		switch (_subformula->formula().getType()) {
        case carl::FormulaType::TRUE: 
			return true;
        case carl::FormulaType::FALSE: {
			this->hasFalse = true;
			FormulaSetT infSubSet;
			infSubSet.insert(_subformula->formula());
			mInfeasibleSubsets.push_back(infSubSet);
			return false;
        }
        case carl::FormulaType::CONSTRAINT: {
			SMTRAT_LOG_FUNC("smtrat.cad", _subformula->formula().constraint());
			if (this->hasFalse) {
				mSubformulaQueue.push_back(_subformula->formula());
				return false;
			} else {
				return this->addConstraintFormula(_subformula->formula());
			}
        }
        default:
			SMTRAT_LOG_ERROR("smtrat.cad", "Asserted " << _subformula->formula());
			assert(false);
			return true;
		}
	}

	/**
	 * All constraints asserted (and not removed)  so far are now added to the CAD object and checked for consistency.
	 * If the result is false, a minimal infeasible subset of the original constraint set is computed.
	 * Otherwise a sample value is available.
	 * @return SAT if consistent, UNSAT otherwise
	 */
	template<typename Settings>
	Answer CADModule<Settings>::checkCore()
	{
		SMTRAT_LOG_FUNC("smtrat.cad", mFullCheck);
		if (!mFullCheck) {
			SMTRAT_LOG_WARN("smtrat.cad", "UNKNOWN due to !mFullCheck");
			return UNKNOWN;
		}
		
		assert(mConstraints.size() == mConstraintsMap.size());
#ifdef SMTRAT_DEVOPTION_Statistics
		mStats->addCall();
#endif
		if (this->hasFalse) return UNSAT;
		else {
			for (const auto& f: mSubformulaQueue) {
				addConstraintFormula(f);
			}
			mSubformulaQueue.clear();
		}
		if (!rReceivedFormula().isRealConstraintConjunction() && !rReceivedFormula().isIntegerConstraintConjunction()) {
			SMTRAT_LOG_WARN("smtrat.cad", "UNKNOWN due to invalid constraints");
			return UNKNOWN;
		}
		if (!mInfeasibleSubsets.empty())
			return UNSAT; // there was no constraint removed which was in a previously generated infeasible subset
		// check the extended constraints for satisfiability
		mCAD.prepareElimination();

		if (variableBounds().isConflicting()) {
			mInfeasibleSubsets.push_back(variableBounds().getConflict());
			mRealAlgebraicSolution = carl::RealAlgebraicPoint<smtrat::Rational>();
			SMTRAT_LOG_DEBUG("smtrat.cad", "Returning UNSAT due to bound conflict.");
			return UNSAT;
		}
		carl::CAD<smtrat::Rational>::BoundMap boundMap;
		std::map<carl::Variable, carl::Interval<smtrat::Rational>> eiMap = mVariableBounds.getEvalIntervalMap();
		std::vector<carl::Variable> variables = mCAD.getVariables();
		for (unsigned v = 0; v < variables.size(); ++v)
		{
			auto vPos = eiMap.find(variables[v]);
			if (vPos != eiMap.end())
				boundMap[v] = vPos->second;
		}
		carl::cad::Answer status = mCAD.check(mConstraints, mRealAlgebraicSolution, mConflictGraph, boundMap, false, true);
		//std::cout << mCAD.getVariables() << " = " << mRealAlgebraicSolution << std::endl;
		if (anAnswerFound()) return ABORTED;
		if (status == carl::cad::Answer::False) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Conflict Graph: " << mConflictGraph);
			cad::MISGeneration<Settings::mis_heuristic> mis;
			mis(*this, mInfeasibleSubsets);
			//std::cout << "Infeasible Subset: " << *mInfeasibleSubsets.begin() << std::endl;
			//std::cout << "From " << constraints() << std::endl;

			if (Settings::checkMISForMinimality) {
				Module::checkInfSubsetForMinimality(mInfeasibleSubsets.begin());
			}
			mRealAlgebraicSolution = carl::RealAlgebraicPoint<smtrat::Rational>();
			SMTRAT_LOG_DEBUG("smtrat.cad", "Returning UNSAT due to theory conflict.");
			SMTRAT_LOG_DEBUG("smtrat.cad", "Subset: " << mInfeasibleSubsets.back());
			return UNSAT;
		}
		if (status == carl::cad::Answer::Unknown) {
			// Pass on branch from CAD.
			const std::vector<carl::Variable>& vars = mCAD.getVariables();
			std::size_t d = vars.size() - mRealAlgebraicSolution.dim();
			assert(vars[d].type() == carl::VariableType::VT_INT);
			auto r = mRealAlgebraicSolution[0].branchingPoint();
			assert(!carl::isInteger(r));
			SMTRAT_LOG_DEBUG("smtrat.cad", "Variables: " << vars);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Branching at " << vars[d] << " = " << r);
			if (mFinalCheck) branchAt(vars[d], r);
			return UNKNOWN;
		}
		SMTRAT_LOG_TRACE("smtrat.cad", "#Samples: " << mCAD.samples().size());
		SMTRAT_LOG_TRACE("smtrat.cad", "Elimination sets:");
		for (unsigned i = 0; i != mCAD.getEliminationSets().size(); ++i) {
			SMTRAT_LOG_TRACE("smtrat.cad", "\tLevel " << i << " (" << mCAD.getEliminationSet(i).size() << "): " << mCAD.getEliminationSet(i));
		}
		SMTRAT_LOG_DEBUG("smtrat.cad", "Result: true");
		SMTRAT_LOG_DEBUG("smtrat.cad", "CAD complete: " << mCAD.isComplete());
		SMTRAT_LOG_DEBUG("smtrat.cad", "Solution point: " << mRealAlgebraicSolution);
		SMTRAT_LOG_DEBUG("smtrat.cad", "Variables: " << mCAD.getVariables());
		mInfeasibleSubsets.clear();
		if (Settings::integerHandling == carl::cad::IntegerHandling::SPLIT_ASSIGNMENT) {
#ifdef SMTRAT_DEVOPTION_Statistics
			{
				std::size_t branches = 0;
				for (std::size_t d = 0; d < mRealAlgebraicSolution.dim(); d++) {
					if (mCAD.getVariables()[d].type() != carl::VariableType::VT_INT) continue;
					if (carl::isInteger(mRealAlgebraicSolution[d])) continue;
					branches++;
				}
				mStats->addBBStats(branches);
			}
#endif
			cad::SplitVariableSelector<Settings::splitHeuristic> svs;
			int d = svs.select(mCAD.getVariables(), mRealAlgebraicSolution);
			if (d != -1) {
				if (mFinalCheck) branchAt(mCAD.getVariables()[std::size_t(d)], mRealAlgebraicSolution[std::size_t(d)].branchingPoint(), true, true, true);
				SMTRAT_LOG_DEBUG("smtrat.cad", "Returning unknown with split");
				return UNKNOWN;
			}
		} else if (Settings::integerHandling == carl::cad::IntegerHandling::SPLIT_PATH) {
			// Check whether the found assignment is integer. Split path to first non-integral assignment
			const std::vector<carl::Variable>& vars = mCAD.getVariables();
			FormulasT formulas;
			FormulasT exclusion;
			for (std::size_t dim = mRealAlgebraicSolution.dim(); dim > 0; dim--) {
				std::size_t d = dim - 1;
				if (!validateIntegrality(vars, d)) {
					// Assemble lemma
					if (mFinalCheck) {
						FormulaT lemma(carl::OR, std::move(formulas));
						FormulaT enforcer(carl::AND, std::move(exclusion));
						SMTRAT_LOG_DEBUG("smtrat.cad", "Lifting lemma " << lemma);
						SMTRAT_LOG_DEBUG("smtrat.cad", "Lifting exclusion " << enforcer);
						SMTRAT_LOG_DEBUG("smtrat.cad", "For sample tree" << mCAD.getSampleTree());
						addLemma(FormulaT(carl::OR, {FormulaT(rReceivedFormula()).negated(), std::move(lemma)}));
						addLemma(enforcer);
					}
					SMTRAT_LOG_DEBUG("smtrat.cad", "Returning unknown with lemma");
					return UNKNOWN;
				}
				auto r = this->mRealAlgebraicSolution[d].branchingPoint();
				Poly p = vars[d] - r;
				FormulaT c1(ConstraintT(p + carl::constant_one<Rational>::get(), carl::Relation::LEQ));
				FormulaT c2(ConstraintT(-p + carl::constant_one<Rational>::get(), carl::Relation::LEQ));
				formulas.push_back(c1);
				formulas.push_back(c2);
				exclusion.push_back(FormulaT(carl::OR, {c1.negated(), c2.negated()}));
			}
		} else if (Settings::integerHandling == carl::cad::IntegerHandling::NONE) {
			const std::vector<carl::Variable>& vars = mCAD.getVariables();
			for (std::size_t d = 0; d < mRealAlgebraicSolution.dim(); d++) {
				if (!validateIntegrality(vars, d)) {
					SMTRAT_LOG_DEBUG("smtrat.cad", "Returning unknown without split");
					return UNKNOWN;
				}
			}
		}
		assert(checkSatisfiabilityOfAssignment());
		SMTRAT_LOG_DEBUG("smtrat.cad", "Returning sat");
		return SAT;
	}

	template<typename Settings>
	void CADModule<Settings>::removeCore(ModuleInput::const_iterator _subformula)
	{
		SMTRAT_LOG_FUNC("smtrat.cad", _subformula->formula());
		switch (_subformula->formula().getType()) {
        case carl::FormulaType::TRUE:
			return;
        case carl::FormulaType::FALSE:
			this->hasFalse = false;
			return;
        case carl::FormulaType::CONSTRAINT: {
			SMTRAT_LOG_FUNC("smtrat.cad", _subformula->formula().constraint());
			auto it = std::find(mSubformulaQueue.begin(), mSubformulaQueue.end(), _subformula->formula());
			if (it != mSubformulaQueue.end()) {
				mSubformulaQueue.erase(it);
				return;
			}

			mVariableBounds.removeBound(_subformula->formula().constraint(), _subformula->formula());

			ConstraintIndexMap::iterator constraintIt = mConstraintsMap.find(_subformula->formula());
			if (constraintIt == mConstraintsMap.end())
				return; // there is nothing to remove
			carl::cad::Constraint<smtrat::Rational> constraint = mConstraints[constraintIt->second];

			SMTRAT_LOG_TRACE("smtrat.cad", "---- Constraint removal (before) ----");
			SMTRAT_LOG_TRACE("smtrat.cad", "Elimination sets:");
			for (unsigned i = 0; i != mCAD.getEliminationSets().size(); ++i) {
				SMTRAT_LOG_TRACE("smtrat.cad", "\tLevel " << i << " (" << mCAD.getEliminationSet(i).size() << "): " << mCAD.getEliminationSet(i));
			}
			SMTRAT_LOG_TRACE("smtrat.cad", "#Samples: " << mCAD.samples().size());
			SMTRAT_LOG_TRACE("smtrat.cad", "-----------------------------------------");
			SMTRAT_LOG_TRACE("smtrat.cad", "Removing " << constraint << "...");

			unsigned constraintIndex = constraintIt->second;
			// remove the constraint in mConstraintsMap
			mConstraintsMap.erase(constraintIt);
			// update the constraint / index map, i.e., decrement all indices above the removed one
			updateConstraintMap(constraintIndex, true);
			// remove the corresponding constraint node with index constraintIndex
			mConflictGraph.removeConstraint(constraint);
			
			// remove the constraint from the list of constraints
			assert(mConstraints.size() > constraintIndex); // the constraint to be removed should be stored in the local constraint list
			mConstraints.erase(mConstraints.begin() + constraintIndex);	// erase the (constraintIt->second)-th element

			// remove the corresponding polynomial from the CAD if it is not occurring in another constraint
			bool doDelete = true;
			for (const auto& c: mConstraints) {
				if (constraint.getPolynomial() == c.getPolynomial()) {
					SMTRAT_LOG_TRACE("smtrat.cad", "Not removing " << constraint.getPolynomial() << " due to " << c);
					doDelete = false;
					break;
				}
			}
			if (doDelete) {
				// no other constraint claims the polynomial, hence remove it from the list and the cad
				mCAD.removePolynomial(constraint.getPolynomial());
			}	

			
			SMTRAT_LOG_TRACE("smtrat.cad", "---- Constraint removal (afterwards) ----");
			SMTRAT_LOG_TRACE("smtrat.cad", "New constraint set: " << mConstraints);
			SMTRAT_LOG_TRACE("smtrat.cad", "Elimination sets:");
			for (unsigned i = 0; i != mCAD.getEliminationSets().size(); ++i) {
				SMTRAT_LOG_TRACE("smtrat.cad", "\tLevel " << i << " (" << mCAD.getEliminationSet(i).size() << "): " << mCAD.getEliminationSet(i));
			}
			SMTRAT_LOG_TRACE("smtrat.cad", "#Samples: " << mCAD.samples().size());
			SMTRAT_LOG_TRACE("smtrat.cad", "-----------------------------------------");
			return;
		}
		default:
			return;
		}
	}

	/**
	 * Updates the model.
	 */
	template<typename Settings>
	void CADModule<Settings>::updateModel() const
	{
		SMTRAT_LOG_FUNC("smtrat.cad", "Updating model");
		clearModel();
		if (this->solverState() == SAT) {
			// bound-independent part of the model
			std::vector<carl::Variable> vars(mCAD.getVariables());
			for (unsigned varID = 0; varID < vars.size(); ++varID) {
				if (varID == mRealAlgebraicSolution.dim()) break;
				ModelValue ass = mRealAlgebraicSolution[varID];
				mModel.insert(std::make_pair(vars[varID], ass));
			}
			// bounds for variables which were not handled in the solution point
			for (auto b: mVariableBounds.getIntervalMap()) {
				// add an assignment for every bound of a variable not in vars (Caution! Destroys vars!)
				std::vector<carl::Variable>::iterator v = std::find(vars.begin(), vars.end(), b.first);
				if (v != vars.end()) {
					vars.erase(v); // shall never be found again
				} else {
					// variable not handled by CAD, use the midpoint of the bounding interval for the assignment
					ModelValue ass = carl::center(b.second);
					mModel.insert(std::make_pair(b.first, ass));
				}
			}
		}
        excludeNotReceivedVariablesFromModel(); // TODO: try to avoid this
		SMTRAT_LOG_DEBUG("smtrat.cad", "Model of CAD: " << mModel);
	}

	///////////////////////
	// Auxiliary methods //
	///////////////////////
	template<typename Settings>
	bool CADModule<Settings>::checkSatisfiabilityOfAssignment() const {
		for (const auto& c: mConstraints) {
			if (!c.satisfiedBy(mRealAlgebraicSolution, mCAD.getVariables())) return false;
		}
		return true;
	}
	
	template<typename Settings>
	bool CADModule<Settings>::addConstraintFormula(const FormulaT& f) {
		assert(f.getType() == carl::FormulaType::CONSTRAINT);
		mVariableBounds.addBound(f.constraint(), f);
		// add the constraint to the local list of constraints and memorize the index/constraint assignment if the constraint is not present already
		if (mConstraintsMap.find(f) != mConstraintsMap.end())
			return true;	// the exact constraint was already considered
		carl::cad::Constraint<smtrat::Rational> constraint = convertConstraint(f.constraint());
		mConstraints.push_back(constraint);
		mConstraintsMap[f] = (unsigned)(mConstraints.size() - 1);
		mCFMap[constraint] = f;
#ifdef __VS
		mCAD.addPolynomial(Poly::PolyType(constraint.getPolynomial()), constraint.getVariables());
#else
		mCAD.addPolynomial(typename Poly::PolyType(constraint.getPolynomial()), constraint.getVariables());
#endif

		return solverState() != UNSAT;
	}

	/**
	 * Converts the constraint types.
	 * @param c constraint of the SMT-RAT
	 * @return constraint of GiNaCRA
	 */
	template<typename Settings>
	inline const carl::cad::Constraint<smtrat::Rational> CADModule<Settings>::convertConstraint( const smtrat::ConstraintT& c )
	{
		// convert the constraints variable
		std::vector<carl::Variable> variables;
		for (auto i: c.variables()) {
			variables.push_back(i);
		}
		carl::Sign signForConstraint = carl::Sign::ZERO;
		bool cadConstraintNegated = false;
		switch (c.relation()) {
			case carl::Relation::EQ: 
				break;
			case carl::Relation::LEQ:
				signForConstraint	= carl::Sign::POSITIVE;
				cadConstraintNegated = true;
				break;
			case carl::Relation::GEQ:
				signForConstraint	= carl::Sign::NEGATIVE;
				cadConstraintNegated = true;
				break;
			case carl::Relation::LESS:
				signForConstraint = carl::Sign::NEGATIVE;
				break;
			case carl::Relation::GREATER:
				signForConstraint = carl::Sign::POSITIVE;
				break;
			case carl::Relation::NEQ:
				cadConstraintNegated = true;
				break;
			default: assert(false);
		}
#ifdef __VS
		return carl::cad::Constraint<smtrat::Rational>((Poly::PolyType)c.lhs(), signForConstraint, variables, cadConstraintNegated);
#else
		return carl::cad::Constraint<smtrat::Rational>((typename Poly::PolyType)c.lhs(), signForConstraint, variables, cadConstraintNegated);
#endif
	}

	/**
	 * Converts the constraint types.
	 * @param c constraint of the GiNaCRA
	 * @return constraint of SMT-RAT
	 */
	template<typename Settings>
	inline ConstraintT CADModule<Settings>::convertConstraint( const carl::cad::Constraint<smtrat::Rational>& c )
	{
		carl::Relation relation = carl::Relation::EQ;
		switch (c.getSign()) {
			case carl::Sign::POSITIVE:
				if (c.isNegated()) relation = carl::Relation::LEQ;
				else relation = carl::Relation::GREATER;
				break;
			case carl::Sign::ZERO:
				if (c.isNegated()) relation = carl::Relation::NEQ;
				else relation = carl::Relation::EQ;
				break;
			case carl::Sign::NEGATIVE:
				if (c.isNegated()) relation = carl::Relation::GEQ;
				else relation = carl::Relation::LESS;
				break;
			default: assert(false);
		}
		return ConstraintT(c.getPolynomial(), relation);
	}

	/**
	 *
	 * @param index
	 * @return
	 */
	template<typename Settings>
	inline const FormulaT& CADModule<Settings>::getConstraintAt(unsigned index) {
		SMTRAT_LOG_TRACE("smtrat.cad", "get " << index << " from " << mConstraintsMap);
                // @todo: Use some other map here.
		for (auto& i: mConstraintsMap) {
			if (i.second == index) // found the entry in the constraint map
				return i.first;
		}
		assert(false);	// The given index should match an input constraint!
		return mConstraintsMap.begin()->first;
	}

	/**
	 * Increment all indices stored in the constraint map being greater than the given index; decrement if decrement is true.
	 * @param index
	 * @param decrement
	 */
	template<typename Settings>
	inline void CADModule<Settings>::updateConstraintMap(unsigned index, bool decrement) {
		SMTRAT_LOG_TRACE("smtrat.cad", "updating " << index << " from " << mConstraintsMap);
		if (decrement) {
			for (auto& i: mConstraintsMap) {
				if (i.second > index) i.second--;
			}
		} else {
			for (auto& i: mConstraintsMap) {
				if (i.second > index) i.second++;
			}
		}
		SMTRAT_LOG_TRACE("smtrat.cad", "now: " << mConstraintsMap);
	}

}	// namespace smtrat

#include "Instantiation.h"
