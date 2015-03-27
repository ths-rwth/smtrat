/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */


/**
 * @file CADModule.cpp
 *
 * @author Ulrich Loup
 * @since 2012-01-19
 * @version 2013-07-10
 */

#include "../../solver/Manager.h"
#include "CADModule.h"

#include <memory>
#include <iostream>

#include "carl/core/logging.h"

using carl::UnivariatePolynomial;
using carl::cad::EliminationSet;
using carl::cad::Constraint;
using carl::Polynomial;
using carl::CAD;
using carl::RealAlgebraicPoint;
using carl::cad::ConflictGraph;

using namespace std;

// CAD settings
//#define SMTRAT_CAD_GENERIC_SETTING
#define SMTRAT_CAD_DISABLE_PROJECTIONORDEROPTIMIZATION
//#define SMTRAT_CAD_DISABLE_MIS
//#define CHECK_SMALLER_MUSES
//#define SMTRAT_CAD_ONEMOSTDEGREEVERTEX_MISHEURISTIC
//#define SMTRAT_CAD_TWOMOSTDEGREEVERTICES_MISHEURISTIC

namespace smtrat
{

	CADModule::CADModule(ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* const _manager):
		Module(_type, _formula, _conditionals, _manager),
		mCAD(_conditionals),
		mConstraints(),
		hasFalse(false),
		subformulaQueue(),
		mConstraintsMap(),
		mRealAlgebraicSolution(),
		mConflictGraph(),
		mVariableBounds()
#ifdef SMTRAT_DEVOPTION_Statistics
		,mStats(CADStatistics::getInstance(0))
#endif
	{
		mInfeasibleSubsets.clear();	// initially everything is satisfied
		// CAD setting
		carl::cad::CADSettings setting = mCAD.getSetting();
		// general setting set
		setting = carl::cad::CADSettings::getSettings(carl::cad::CADSettingsType::BOUNDED); // standard
		setting.simplifyByFactorization = true;
		setting.simplifyByRootcounting  = true;

		#ifdef SMTRAT_CAD_DISABLE_MIS
			setting.computeConflictGraph = false;
		#else
			setting.computeConflictGraph = true;
		#endif

		setting.trimVariables = false; // maintains the dimension important for the constraint checking
//		setting.autoSeparateEquations = false; // <- @TODO: find a correct implementation of the MIS for the only-strict or only-equations optimizations

		#ifndef SMTRAT_CAD_DISABLE_PROJECTIONORDEROPTIMIZATION
		// variable order optimization
		std::forward_list<symbol> variables = std::forward_list<symbol>( );
		GiNaC::symtab allVariables = mpReceivedFormula->constraintPool().realVariables();
		for( GiNaC::symtab::const_iterator i = allVariables.begin(); i != allVariables.end(); ++i )
			variables.push_front( GiNaC::ex_to<symbol>( i->second ) );
		std::forward_list<Poly> polynomials = std::forward_list<Poly>( );
		for( fcs_const_iterator i = mpReceivedFormula->constraintPool().begin(); i != mpReceivedFormula->constraintPool().end(); ++i )
			polynomials.push_front( (*i)->lhs() );
		mCAD = CAD( {}, CAD::orderVariablesGreeedily( variables.begin(), variables.end(), polynomials.begin(), polynomials.end() ), _conditionals, setting );
		#ifdef MODULE_VERBOSE
		cout << "Optimizing CAD variable order from ";
		for( forward_list<GiNaC::symbol>::const_iterator k = variables.begin(); k != variables.end(); ++k )
			cout << *k << " ";
		cout << "  to   ";
		for( vector<GiNaC::symbol>::const_iterator k = mCAD.variablesScheduled().begin(); k != mCAD.variablesScheduled().end(); ++k )
			cout << *k << " ";
		cout << endl;;
		#endif
		#else
		mCAD.alterSetting(setting);
		#endif

		SMTRAT_LOG_TRACE("smtrat.cad", "Initial CAD setting:" << std::endl << setting);
		#ifdef SMTRAT_CAD_GENERIC_SETTING
		SMTRAT_LOG_TRACE("smtrat.cad", "SMTRAT_CAD_GENERIC_SETTING set");
		#endif
		#ifdef SMTRAT_CAD_DISABLE_PROJECTIONORDEROPTIMIZATION
		SMTRAT_LOG_TRACE("smtrat.cad", "SMTRAT_CAD_DISABLE_PROJECTIONORDEROPTIMIZATION set");
		#endif
		#ifdef SMTRAT_CAD_DISABLE_MIS
		SMTRAT_LOG_TRACE("smtrat.cad", "SMTRAT_CAD_DISABLE_MIS set");
		#endif
	}

	CADModule::~CADModule(){}

	/**
	 * This method just adds the respective constraint of the subformula, which ought to be one real constraint,
	 * to the local list of constraints. Moreover, the list of all variables is updated accordingly.
	 *
	 * Note that the CAD object is not touched here, the respective calls to CAD::addPolynomial and CAD::check happen in isConsistent.
	 * @param _subformula
	 * @return returns false if the current list of constraints was already found to be unsatisfiable (in this case, nothing is done), returns true previous result if the constraint was already checked for consistency before, otherwise true
	 */
	bool CADModule::addCore(ModuleInput::const_iterator _subformula)
	{
		SMTRAT_LOG_FUNC("smtrat.cad", _subformula->formula());
		switch (_subformula->formula().getType()) {
                    case carl::FormulaType::TRUE: 
			return true;
                    case carl::FormulaType::FALSE: {
			this->hasFalse = true;
			FormulasT infSubSet;
			infSubSet.insert(_subformula->formula());
			mInfeasibleSubsets.push_back(infSubSet);
			return false;
                    }
                    case carl::FormulaType::CONSTRAINT: {
			if (this->hasFalse) {
				this->subformulaQueue.insert(_subformula->formula());
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
         * @param _full false, if this module should avoid too expensive procedures and rather return unknown instead.
	 * @return True if consistent, False otherwise
	 */
	Answer CADModule::checkCore( bool _full )
	{
		if (this->hasFalse) return False;
		else {
			for (auto f: this->subformulaQueue) {
				this->addConstraintFormula(f);
			}
			this->subformulaQueue.clear();
		}
		//std::cout << "CAD has:" << std::endl;
		//for (auto c: this->mConstraints) std::cout << "\t\t" << c << std::endl;
		//this->printReceivedFormula();
		if (!rReceivedFormula().isRealConstraintConjunction() && !rReceivedFormula().isIntegerConstraintConjunction()) {
			return Unknown;
		}
		if (!mInfeasibleSubsets.empty())
			return False; // there was no constraint removed which was in a previously generated infeasible subset
		// perform the scheduled elimination and see if there were new variables added
		if (mCAD.prepareElimination())
			mConflictGraph.clearSampleVertices(); // all sample vertices are now invalid, thus remove them
		// check the extended constraints for satisfiability

		if (variableBounds().isConflicting()) {
			mInfeasibleSubsets.push_back(variableBounds().getConflict());
			mRealAlgebraicSolution = carl::RealAlgebraicPoint<smtrat::Rational>();
			return False;
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
		if (!mCAD.check(mConstraints, mRealAlgebraicSolution, mConflictGraph, boundMap, false, true))
		{
			#ifdef SMTRAT_CAD_DISABLE_MIS
			// construct a trivial infeasible subset
			FormulasT boundConstraints = mVariableBounds.getOriginsOfBounds();
			mInfeasibleSubsets.push_back( FormulasT() );
			for (auto i:mConstraintsMap)
			{
				mInfeasibleSubsets.back().insert( i.first );
			}
			mInfeasibleSubsets.back().insert( boundConstraints.begin(), boundConstraints.end() );
			#else
			// construct an infeasible subset
			assert(mCAD.getSetting().computeConflictGraph);
			// copy conflict graph for destructive heuristics and invert it
			ConflictGraph g(mConflictGraph);
			g.invert();
			#if defined SMTRAT_CAD_ONEMOSTDEGREEVERTEX_MISHEURISTIC
				// remove the lowest-degree vertex (highest degree in inverted graph)
				g.removeConstraintVertex(g.maxDegreeVertex());
			#elif defined SMTRAT_CAD_TWOMOSTDEGREEVERTICES_MISHEURISTIC
				// remove the two lowest-degree vertices (highest degree in inverted graph)
				g.removeConstraintVertex(g.maxDegreeVertex());
				g.removeConstraintVertex(g.maxDegreeVertex());
			#else
				// remove last vertex, assuming it is part of the MIS
				assert(mConstraints.size() > 0);
				g.removeConstraintVertex(mConstraints.size() - 1);
			#endif
			
			SMTRAT_LOG_DEBUG("smtrat.cad", "Input: " << mConstraints);
			for (auto j: mConstraints) SMTRAT_LOG_DEBUG("smtrat.cad", "\t" << j);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Bounds: " << mVariableBounds);
				
			std::vector<FormulasT> infeasibleSubsets = extractMinimalInfeasibleSubsets_GreedyHeuristics(g);

			FormulasT boundConstraints = mVariableBounds.getOriginsOfBounds();
			for (auto i: infeasibleSubsets) {
                #ifdef LOGGING_CARL
				SMTRAT_LOG_DEBUG("smtrat.cad", "Infeasible:");
				for (auto j: i) SMTRAT_LOG_DEBUG("smtrat.cad", "\t" << j);
                #endif
				mInfeasibleSubsets.push_back(i);
				mInfeasibleSubsets.back().insert(boundConstraints.begin(), boundConstraints.end());
			}

			#ifdef CHECK_SMALLER_MUSES
			Module::checkInfSubsetForMinimality(mInfeasibleSubsets->begin());
			#endif
			#endif
			mRealAlgebraicSolution = carl::RealAlgebraicPoint<smtrat::Rational>();
			return False;
		}
		SMTRAT_LOG_TRACE("smtrat.cad", "#Samples: " << mCAD.samples().size());
		SMTRAT_LOG_TRACE("smtrat.cad", "Elimination sets:");
		for (unsigned i = 0; i != mCAD.getEliminationSets().size(); ++i) {
			SMTRAT_LOG_TRACE("smtrat.cad", "\tLevel " << i << " (" << mCAD.getEliminationSet(i).size() << "): " << mCAD.getEliminationSet(i));
		}
		SMTRAT_LOG_TRACE("smtrat.cad", "Result: true");
		SMTRAT_LOG_TRACE("smtrat.cad", "CAD complete: " << mCAD.isComplete());
		SMTRAT_LOG_TRACE("smtrat.cad", "Solution point: " << mRealAlgebraicSolution);
		mInfeasibleSubsets.clear();
#ifdef SMTRAT_CAD_ENABLE_INTEGER
		if (rReceivedFormula().isIntegerConstraintConjunction()) {
			// Check whether the found assignment is integer.
			std::vector<carl::Variable> vars(mCAD.getVariables());
			for (unsigned d = 0; d < this->mRealAlgebraicSolution.dim(); d++) {
				auto r = this->mRealAlgebraicSolution[d]->branchingPoint();
				if (!carl::isInteger(r)) {
					branchAt(vars[d], r);
					return Unknown;
				}
			}
		}
#endif
		return True;
	}

	void CADModule::removeCore(ModuleInput::const_iterator _subformula)
	{
		switch (_subformula->formula().getType()) {
                    case carl::FormulaType::TRUE:
			return;
                    case carl::FormulaType::FALSE:
			this->hasFalse = false;
			return;
                    case carl::FormulaType::CONSTRAINT: {
			auto it = this->subformulaQueue.find(_subformula->formula());
			if (it != this->subformulaQueue.end()) {
				this->subformulaQueue.erase(it);
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
			// remove the constraint from the list of constraints
			assert(mConstraints.size() > constraintIndex); // the constraint to be removed should be stored in the local constraint list
			mConstraints.erase(mConstraints.begin() + constraintIndex);	// erase the (constraintIt->second)-th element
			// update the constraint / index map, i.e., decrement all indices above the removed one
			updateConstraintMap(constraintIndex, true);
			// remove the corresponding constraint node with index constraintIndex
			mConflictGraph.removeConstraintVertex(constraintIndex);
			// remove the corresponding polynomial from the CAD if it is not occurring in another constraint
			bool doDelete = true;

			///@todo Why was this iteration reversed?
			for (auto c: mConstraints) {
				if (constraint.getPolynomial() == c.getPolynomial()) {
					doDelete = false;
					break;
				}
			}
			if (doDelete) // no other constraint claims the polynomial, hence remove it from the list and the cad
				mCAD.removePolynomial(constraint.getPolynomial());

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
	void CADModule::updateModel() const
	{
		clearModel();
		if (this->solverState() == True) {
			// bound-independent part of the model
			std::vector<carl::Variable> vars(mCAD.getVariables());
			for (unsigned varID = 0; varID < vars.size(); ++varID) {
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
					ModelValue ass = b.second.center();
					mModel.insert(std::make_pair(b.first, ass));
				}
			}
		}
	}

	///////////////////////
	// Auxiliary methods //
	///////////////////////
	
	bool CADModule::addConstraintFormula(const FormulaT& f) {
		assert(f.getType() == carl::FormulaType::CONSTRAINT);
		mVariableBounds.addBound(f.constraint(), f);
		// add the constraint to the local list of constraints and memorize the index/constraint assignment if the constraint is not present already
		if (mConstraintsMap.find(f) != mConstraintsMap.end())
			return true;	// the exact constraint was already considered
		carl::cad::Constraint<smtrat::Rational> constraint = convertConstraint(f.constraint());
		mConstraints.push_back(constraint);
		mConstraintsMap[f] = (unsigned)(mConstraints.size() - 1);
		mCAD.addPolynomial(typename Poly::PolyType(constraint.getPolynomial()), constraint.getVariables());
		mConflictGraph.addConstraintVertex(); // increases constraint index internally what corresponds to adding a new constraint node with index mConstraints.size()-1

		return solverState() != False;
	}

	/**
	 * Converts the constraint types.
	 * @param c constraint of the SMT-RAT
	 * @return constraint of GiNaCRA
	 */
	inline const carl::cad::Constraint<smtrat::Rational> CADModule::convertConstraint( const smtrat::ConstraintT& c )
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
		return carl::cad::Constraint<smtrat::Rational>((typename Poly::PolyType)c.lhs(), signForConstraint, variables, cadConstraintNegated);
	}

	/**
	 * Converts the constraint types.
	 * @param c constraint of the GiNaCRA
	 * @return constraint of SMT-RAT
	 */
	inline ConstraintT CADModule::convertConstraint( const carl::cad::Constraint<smtrat::Rational>& c )
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
	 * Computes an infeasible subset of the current set of constraints by approximating a vertex cover of the given conflict graph.
	 * 
	 * Caution! The method is destructive with regard to the conflict graph.
	 *
	 * Heuristics:
	 * Select the highest-degree vertex for the vertex cover and remove it as long as we have edges in the graph.
	 *
	 * @param conflictGraph the conflict graph is destroyed during the computation
	 * @return an infeasible subset of the current set of constraints
	 */
	inline std::vector<FormulasT> CADModule::extractMinimalInfeasibleSubsets_GreedyHeuristics( ConflictGraph& conflictGraph )
	{
		// initialize MIS with the last constraint
		std::vector<FormulasT> mis = std::vector<FormulasT>(1, FormulasT());
		mis.front().insert(getConstraintAt((unsigned)(mConstraints.size() - 1)));	// the last constraint is assumed to be always in the MIS
		if (mConstraints.size() > 1) {
			// construct set cover by greedy heuristic
			std::list<ConflictGraph::Vertex> setCover;
			long unsigned vertex = conflictGraph.maxDegreeVertex();
			while (conflictGraph.degree(vertex) > 0) {
				// add v to the setCover
				setCover.push_back(vertex);
				// remove coverage information of v from conflictGraph
				conflictGraph.invertConflictingVertices(vertex);
				SMTRAT_LOG_TRACE("smtrat.cad", "Conflict graph after removal of " << vertex << ": " << endl << conflictGraph);
				// get the new vertex with the biggest number of adjacent solution point vertices
				vertex = conflictGraph.maxDegreeVertex();
			}
			// collect constraints according to the vertex cover
			for (auto v: setCover)
				mis.front().insert(getConstraintAt((unsigned)(v)));
		}
		return mis;
	}

	/**
	 *
	 * @param index
	 * @return
	 */
	inline const FormulaT& CADModule::getConstraintAt(unsigned index) {
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
	inline void CADModule::updateConstraintMap(unsigned index, bool decrement) {
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
