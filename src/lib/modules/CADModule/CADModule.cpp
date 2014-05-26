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

//#define MODULE_VERBOSE

#include "../../Manager.h"
#include "CADModule.h"

#include <memory>
#include <iostream>

using carl::UnivariatePolynomial;
using carl::cad::EliminationSet;
using carl::cad::Constraint;
using carl::Polynomial;
using carl::CAD;
using carl::RealAlgebraicPoint;
using carl::cad::ConflictGraph;

using namespace std;

// CAD settings
//#define SMTRAT_CAD_ALTERNATIVE_SETTING
//#define SMTRAT_CAD_DISABLEEQUATIONDETECT_SETTING
//#define SMTRAT_CAD_GENERIC_SETTING
#define SMTRAT_CAD_DISABLE_PROJECTIONORDEROPTIMIZATION
//#define SMTRAT_CAD_DISABLE_SMT
#define SMTRAT_CAD_DISABLE_THEORYPROPAGATION
//#define SMTRAT_CAD_DISABLE_MIS
//#define CHECK_SMALLER_MUSES
//#define SMTRAT_CAD_ONEMOSTDEGREEVERTEX_MISHEURISTIC
//#define SMTRAT_CAD_TWOMOSTDEGREEVERTICES_MISHEURISTIC
#ifdef SMTRAT_CAD_DISABLE_SMT
    #define SMTRAT_CAD_DISABLE_THEORYPROPAGATION
    #define SMTRAT_CAD_DISABLE_MIS
#endif

namespace smtrat
{

    CADModule::CADModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* const _manager ):
        Module( _type, _formula, _conditionals, _manager ),
        mCAD( _conditionals ),
        mConstraints(),
        mConstraintsMap(),
        mRealAlgebraicSolution(),
        mConflictGraph()
        #ifdef SMTRAT_CAD_VARIABLEBOUNDS
        ,
        mVariableBounds()
        #endif
#ifdef SMTRAT_DEVOPTION_Statistics
               ,mStats(CADStatistics::getInstance(0))
#endif
    {
        mInfeasibleSubsets.clear();    // initially everything is satisfied
        // CAD setting
        carl::cad::CADSettings setting = mCAD.getSetting();
        // general setting set
        #ifdef SMTRAT_CAD_ALTERNATIVE_SETTING
            setting = carl::cad::CADSettings::getSettings( carl::cad::CADSettingsType::RATIONALSAMPLE );
        #else
            #ifdef SMTRAT_CAD_DISABLEEQUATIONDETECT_SETTING
                setting = carl::cad::CADSettings::getSettings( carl::cad::CADSettingsType::GENERIC );
            #else
                #ifdef SMTRAT_CAD_VARIABLEBOUNDS
                setting = carl::cad::CADSettings::getSettings( carl::cad::CADSettingsType::BOUNDED ); // standard
                #else
                setting = carl::cad::CADSettings::getSettings( carl::cad::CADSettingsType::EQUATIONDETECT ); // standard
                #endif
                setting.computeConflictGraph    = true;
                setting.numberOfDeductions      = 1;
                setting.warmRestart             = true;
                setting.simplifyByFactorization = true;
                setting.simplifyByRootcounting  = true;
            #endif
        #endif

        // single settings altered
        #ifdef SMTRAT_CAD_DISABLE_THEORYPROPAGATION
            setting.numberOfDeductions = 0;
        #else
            setting.numberOfDeductions = 1;
        #endif
        #ifdef SMTRAT_CAD_DISABLE_MIS
            setting.computeConflictGraph = false;
        #else
            setting.computeConflictGraph = true;
        #endif

        setting.trimVariables = false; // maintains the dimension important for the constraint checking
//        setting.autoSeparateEquations = false; // <- @TODO: find a correct implementation of the MIS for the only-strict or only-equations optimizations

        #ifndef SMTRAT_CAD_DISABLE_PROJECTIONORDEROPTIMIZATION
        // variable order optimization
        std::forward_list<symbol> variables = std::forward_list<symbol>( );
        GiNaC::symtab allVariables = mpReceivedFormula->constraintPool().realVariables();
        for( GiNaC::symtab::const_iterator i = allVariables.begin(); i != allVariables.end(); ++i )
            variables.push_front( GiNaC::ex_to<symbol>( i->second ) );
        std::forward_list<Polynomial> polynomials = std::forward_list<Polynomial>( );
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
        mCAD.alterSetting( setting );
        #endif
        #ifdef MODULE_VERBOSE
        cout << "Initial CAD setting: " << endl << setting << endl;
        #ifdef SMTRAT_CAD_ALTERNATIVE_SETTING
        cout << "SMTRAT_CAD_ALTERNATIVE_SETTING set" << endl;
        #endif
        #ifdef SMTRAT_CAD_DISABLEEQUATIONDETECT_SETTING
        cout << "SMTRAT_CAD_DISABLEEQUATIONDETECT_SETTING set" << endl;
        #endif
        #ifdef SMTRAT_CAD_GENERIC_SETTING
        cout << "SMTRAT_CAD_GENERIC_SETTING set" << endl;
        #endif
        #ifdef SMTRAT_CAD_DISABLE_PROJECTIONORDEROPTIMIZATION
        cout << "SMTRAT_CAD_DISABLE_PROJECTIONORDEROPTIMIZATION set" << endl;
        #endif
        #ifdef SMTRAT_CAD_DISABLE_SMT
        cout << "SMTRAT_CAD_DISABLE_SMT set" << endl;
        #endif
        #ifdef SMTRAT_CAD_DISABLE_MIS
        cout << "SMTRAT_CAD_DISABLE_MIS set" << endl;
        #endif
        #ifdef SMTRAT_CAD_DISABLE_MIS
        cout << "SMTRAT_CAD_DISABLE_MIS set" << endl;
        #endif
        
        #define SMTRAT_CAD_DISABLE_THEORYPROPAGATION
        //#define SMTRAT_CAD_DISABLE_MIS
        //#define CHECK_SMALLER_MUSES
        //#define SMTRAT_CAD_ONEMOSTDEGREEVERTEX_MISHEURISTIC
        //#define SMTRAT_CAD_TWOMOSTDEGREEVERTICES_MISHEURISTIC
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
    bool CADModule::assertSubformula( ModuleInput::const_iterator _subformula )
    {
        assert( (*_subformula)->getType() == CONSTRAINT );
        Module::assertSubformula( _subformula );
        #ifdef SMTRAT_CAD_VARIABLEBOUNDS
        mVariableBounds.addBound( (*_subformula)->pConstraint(), *_subformula );
        #endif
        if( solverState() == False )
            return false;
        // add the constraint to the local list of constraints and memorize the index/constraint assignment if the constraint is not present already
        if( mConstraintsMap.find( _subformula ) != mConstraintsMap.end() )
            return true;    // the exact constraint was already considered
        carl::cad::Constraint<smtrat::Rational> constraint = convertConstraint( (*_subformula)->constraint() );
        mConstraints.push_back( constraint );
        mConstraintsMap[ _subformula ] = mConstraints.size() - 1;
        mCAD.addPolynomial(Polynomial(constraint.getPolynomial()), constraint.getVariables());
        mConflictGraph.addConstraintVertex(); // increases constraint index internally what corresponds to adding a new constraint node with index mConstraints.size()-1
        return true;
    }

    /**
     * All constraints asserted (and not removed)  so far are now added to the CAD object and checked for consistency.
     * If the result is false, a minimal infeasible subset of the original constraint set is computed.
     * Otherwise a sample value is available.
     * @return True if consistent, False otherwise
     */
    Answer CADModule::isConsistent()
    {
        if( !mpReceivedFormula->isRealConstraintConjunction() )
            return foundAnswer( Unknown );
        if( !mInfeasibleSubsets.empty() )
            return foundAnswer( False ); // there was no constraint removed which was in a previously generated infeasible subset
        // perform the scheduled elimination and see if there were new variables added
        if( mCAD.prepareElimination() )
            mConflictGraph.clearSampleVertices(); // all sample vertices are now invalid, thus remove them
        // check the extended constraints for satisfiability
        #ifdef SMTRAT_CAD_VARIABLEBOUNDS
        if( variableBounds().isConflicting() )
        {
            mInfeasibleSubsets.push_back( variableBounds().getConflict() );
            mRealAlgebraicSolution = carl::RealAlgebraicPoint<smtrat::Rational>();
            return foundAnswer( False );
        }
		carl::CAD<smtrat::Rational>::BoundMap boundMap;
        std::map<carl::Variable, carl::Interval<smtrat::Rational>> eiMap = mVariableBounds.getEvalIntervalMap();
        std::vector<carl::Variable> variables = mCAD.getVariables();
        for (unsigned v = 0; v < variables.size(); ++v)
        {
            auto vPos = eiMap.find( variables[v] );
            if (vPos != eiMap.end())
                boundMap[v] = vPos->second;
        }
        #endif
        list<pair<list<carl::cad::Constraint<smtrat::Rational>>, list<carl::cad::Constraint<smtrat::Rational>> > > deductions;
        #ifdef SMTRAT_CAD_VARIABLEBOUNDS
        if( !mCAD.check( mConstraints, mRealAlgebraicSolution, mConflictGraph, boundMap, deductions, false, false ) )
        #else
        if( !mCAD.check( mConstraints, mRealAlgebraicSolution, mConflictGraph, deductions, false, false ) )
        #endif
        {
            #ifdef SMTRAT_CAD_DISABLE_SMT
            // simulate non-incrementality by constructing a trivial infeasible subset and clearing all data in the CAD
            #define SMTRAT_CAD_DISABLE_MIS // this constructs a trivial infeasible subset below
            #define SMTRAT_CAD_DISABLE_THEORYPROPAGATION // no lemmata from staisfying assignments are going to be constracted
            mCAD.clear();
            // replay adding the polynomials as scheduled polynomials
            for( vector<carl::cad::Constraint<smtrat::Rational>>::const_iterator constraint = mConstraints.begin(); constraint != mConstraints.end(); ++constraint )
                mCAD.addPolynomial( constraint->getPolynomial(), constraint->getVariables() );
            #endif
            #ifdef SMTRAT_CAD_DISABLE_MIS
            // construct a trivial infeasible subset
            #ifdef SMTRAT_CAD_VARIABLEBOUNDS
            PointerSet<Formula> boundConstraints = mVariableBounds.getOriginsOfBounds();
            #endif
            mInfeasibleSubsets.push_back( PointerSet<Formula>() );
            for( ConstraintIndexMap::const_iterator i = mConstraintsMap.begin(); i != mConstraintsMap.end(); ++i )
            {
                mInfeasibleSubsets.back().insert( *i->first );
            }
            #ifdef SMTRAT_CAD_VARIABLEBOUNDS
            mInfeasibleSubsets.back().insert( boundConstraints.begin(), boundConstraints.end() );
            #endif
            #else
            // construct an infeasible subset
            assert( mCAD.getSetting().computeConflictGraph );
            // copy conflict graph for destructive heuristics and invert it
            ConflictGraph g = ConflictGraph( mConflictGraph );
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
                g.removeConstraintVertex(mConstraints.size()-1);
            #endif
            
            vec_set_const_pFormula infeasibleSubsets = extractMinimalInfeasibleSubsets_GreedyHeuristics( g );

            #ifdef SMTRAT_CAD_VARIABLEBOUNDS
            PointerSet<Formula> boundConstraints = mVariableBounds.getOriginsOfBounds();
            #endif
            for( vec_set_const_pFormula::const_iterator i = infeasibleSubsets.begin(); i != infeasibleSubsets.end(); ++i )
            {
                mInfeasibleSubsets.push_back( *i );
                #ifdef SMTRAT_CAD_VARIABLEBOUNDS
                mInfeasibleSubsets.back().insert( boundConstraints.begin(), boundConstraints.end() );
                #endif
            }

            #ifdef CHECK_SMALLER_MUSES
            Module::checkInfSubsetForMinimality( mInfeasibleSubsets->begin() );
            #endif
            #endif
            mRealAlgebraicSolution = carl::RealAlgebraicPoint<smtrat::Rational>();
            return foundAnswer( False );
        }
        #ifdef MODULE_VERBOSE
        cout << endl << "#Samples: " << mCAD.samples().size() << endl;
        cout << "Elimination sets:" << endl;
        vector<EliminationSet> elimSets = mCAD.eliminationSets();
        for( unsigned i = 0; i != elimSets.size(); ++i )
            cout << "  Level " << i << " (" << elimSets[i].size() << "): " << elimSets[i] << endl;
        cout << "Result: true" << endl;
        cout << "CAD complete: " << mCAD.isComplete() << endl;
        cout << "Solution point: " << mRealAlgebraicSolution << endl << endl;
//        mCAD.printSampleTree();
        #endif
        mInfeasibleSubsets.clear();
        #ifndef SMTRAT_CAD_DISABLE_THEORYPROPAGATION
        // compute theory deductions
        assert( mCAD.setting().numberOfDeductions > 0 );
        #ifdef MODULE_VERBOSE
        cout << "Constructing theory deductions..." << endl;
        #endif
        this->addDeductions( deductions );
        #endif
        return foundAnswer( anAnswerFound() ? Unknown : True );
    }

    void CADModule::removeSubformula( ModuleInput::const_iterator _subformula )
    {
        if ((*_subformula)->getType() != CONSTRAINT)
        { // not our concern
            Module::removeSubformula( _subformula );
            return;
        }
        #ifdef SMTRAT_CAD_VARIABLEBOUNDS
		mVariableBounds.removeBound( (*_subformula)->pConstraint(), *_subformula );
        #endif

        ConstraintIndexMap::iterator constraintIt = mConstraintsMap.find( _subformula );
        if( constraintIt == mConstraintsMap.end() )
            return; // there is nothing to remove
        carl::cad::Constraint<smtrat::Rational> constraint = mConstraints[constraintIt->second];
        #ifdef MODULE_VERBOSE
        cout << endl << "---- Constraint removal (before) ----" << endl;
        cout << "Elimination set sizes:";
        vector<EliminationSet> elimSets = mCAD.eliminationSets();
        for( unsigned i = 0; i != elimSets.size(); ++i )
            cout << "  Level " << i << " (" << elimSets[i].size() << "): " << elimSets[i] << endl;
        cout << endl << "#Samples: " << mCAD.samples().size() << endl;
        cout << "-----------------------------------------" << endl;
        cout << "Removing " << constraint << "..." << endl;
        #endif
        unsigned constraintIndex = constraintIt->second;
        // remove the constraint in mConstraintsMap
        mConstraintsMap.erase( constraintIt );
        // remove the constraint from the list of constraints
        assert( mConstraints.size() > constraintIndex ); // the constraint to be removed should be stored in the local constraint list
        mConstraints.erase( mConstraints.begin() + constraintIndex );    // erase the (constraintIt->second)-th element
        // update the constraint / index map, i.e., decrement all indices above the removed one
        updateConstraintMap( constraintIndex, true );
        // remove the corresponding constraint node with index constraintIndex
        mConflictGraph.removeConstraintVertex(constraintIndex);
        // remove the corresponding polynomial from the CAD if it is not occurring in another constraint
        bool doDelete = true;
        for( vector<carl::cad::Constraint<smtrat::Rational>>::const_reverse_iterator c = mConstraints.rbegin(); c != mConstraints.rend(); ++c )
        {
            if( constraint.getPolynomial() == c->getPolynomial() )
            {
                doDelete = false;
                break;
            }
        }
        if( doDelete ) // no other constraint claims the polynomial, hence remove it from the list and the cad
            mCAD.removePolynomial( constraint.getPolynomial() );
        #ifdef MODULE_VERBOSE
        cout << endl << "---- Constraint removal (afterwards) ----" << endl;
        cout << "New constraint set:" << endl;
        for( auto k = mConstraints.begin(); k != mConstraints.end(); ++k )
            cout << " " << *k << endl;
        cout << "Elimination sets:";
        elimSets = mCAD.eliminationSets();
        for( unsigned i = 0; i != elimSets.size(); ++i )
            cout << "  Level " << i << " (" << elimSets[i].size() << "): " << elimSets[i] << endl;
        cout << endl << "#Samples: " << mCAD.samples().size() << endl;
        cout << "-----------------------------------------" << endl;
        #endif
        Module::removeSubformula( _subformula );
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
                Assignment ass = mRealAlgebraicSolution[varID];
				mModel.insert(std::make_pair(vars[varID], ass));
            }
            #ifdef SMTRAT_CAD_VARIABLEBOUNDS
            // bounds for variables which were not handled in the solution point
            for (auto b: mVariableBounds.getIntervalMap())
            { // add an assignment for every bound of a variable not in vars (Caution! Destroys vars!)
                std::vector<carl::Variable>::iterator v = std::find(vars.begin(), vars.end(), b.first);
                if( v != vars.end() )
                    vars.erase( v ); // shall never be found again
                else
                { // variable not handled by CAD, use the midpoint of the bounding interval for the assignment
                    Assignment ass = b.second.center();
					mModel.insert(std::make_pair(b.first, ass));
                }
            }
            #endif
        }
    }

    ///////////////////////
    // Auxiliary methods //
    ///////////////////////

    /**
     * Converts the constraint types.
     * @param c constraint of the SMT-RAT
     * @return constraint of GiNaCRA
     */
    inline const carl::cad::Constraint<smtrat::Rational> CADModule::convertConstraint( const smtrat::Constraint& c )
    {
        // convert the constraints variable
        std::vector<carl::Variable> variables;
        for (auto i: c.variables()) {
            variables.push_back(i);
        }
        carl::Sign signForConstraint = carl::Sign::ZERO;
        bool cadConstraintNegated = false;
        switch (c.relation())
        {
		case Relation::EQ: 
			break;
		case Relation::LEQ: {
                signForConstraint    = carl::Sign::POSITIVE;
                cadConstraintNegated = true;
                break;
            }
		case Relation::GEQ: {
                signForConstraint    = carl::Sign::NEGATIVE;
                cadConstraintNegated = true;
                break;
            }
		case Relation::LESS: {
                signForConstraint = carl::Sign::NEGATIVE;
                break;
            }
		case Relation::GREATER: {
                signForConstraint = carl::Sign::POSITIVE;
                break;
            }
		case Relation::NEQ: {
                cadConstraintNegated = true;
                break;
            }
        default: assert(false);
        }
        return carl::cad::Constraint<smtrat::Rational>(c.lhs(), signForConstraint, variables, cadConstraintNegated);
    }

    /**
     * Converts the constraint types.
     * @param c constraint of the GiNaCRA
     * @return constraint of SMT-RAT
     */
    inline const Constraint* CADModule::convertConstraint( const carl::cad::Constraint<smtrat::Rational>& c )
    {
        Relation relation = Relation::EQ;
        switch (c.getSign()) {
		case carl::Sign::POSITIVE:
            {
                if (c.isNegated())
                    relation = Relation::LEQ;
                else
                    relation = Relation::GREATER;
                break;
            }
            case carl::Sign::ZERO:
            {
                if (c.isNegated())
                    relation = Relation::NEQ;
                else
                    relation = Relation::EQ;
                break;
            }
            case carl::Sign::NEGATIVE:
            {
                if (c.isNegated())
                    relation = Relation::GEQ;
                else
                    relation = Relation::NEQ;
                break;
            }
            default: assert(false);
        }
        return newConstraint(Polynomial(c.getPolynomial()), relation);
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
    inline vec_set_const_pFormula CADModule::extractMinimalInfeasibleSubsets_GreedyHeuristics( ConflictGraph& conflictGraph )
    {
        // initialize MIS with the last constraint
        vec_set_const_pFormula mis = vec_set_const_pFormula( 1, PointerSet<Formula>() );
        mis.front().insert( getConstraintAt( mConstraints.size() - 1 ) );    // the last constraint is assumed to be always in the MIS
        if( mConstraints.size() > 1 )
        { // construct set cover by greedy heuristic
            list<ConflictGraph::Vertex> setCover = list<ConflictGraph::Vertex>();
            long unsigned vertex = conflictGraph.maxDegreeVertex();
            while( conflictGraph.degree( vertex ) > 0 )
            {
                // add v to the setCover
                setCover.push_back( vertex );
                // remove coverage information of v from conflictGraph
                conflictGraph.invertConflictingVertices( vertex );
                #ifdef MODULE_VERBOSE
                cout << "Conflict graph after removal of " << vertex << ": " << endl << conflictGraph << endl << endl;
                #endif
                // get the new vertex with the biggest number of adjacent solution point vertices
                vertex = conflictGraph.maxDegreeVertex();
            }
            // collect constraints according to the vertex cover
            for( list<ConflictGraph::Vertex>::const_iterator v = setCover.begin(); v != setCover.end(); ++v )
                mis.front().insert( getConstraintAt( *v ) );
        }
        return mis;
    }

    void CADModule::addDeductions( const list<pair<list<carl::cad::Constraint<smtrat::Rational>>, list<carl::cad::Constraint<smtrat::Rational>> > >& deductions )
    {
        for (auto implication: deductions)
        {
            assert( ( !implication.first.empty() && !implication.second.empty() ) || implication.first.size() > 1 || implication.second.size() > 1  );
            PointerSet<Formula> subformulas;
            // process A in A => B
            for (auto constraint: implication.first)
            {
                // check whether the given constraint is one of the input constraints
                unsigned index = 0;
                for ( ; index < mConstraints.size(); ++index)
                    if (mConstraints[index] == constraint)
                        break;
                if (mConstraints.size() != index)
                { // the constraint matches the input constraint at position i
                    for (auto i: mConstraintsMap)
                    {
                        if (i.second == index) // found the entry in the constraint map
                        {
                            subformulas.insert(newNegation(newFormula((*i.first)->pConstraint())));
                            break;
                        }
                    }
                }
                else // add a new constraint
                    subformulas.insert(newFormula(convertConstraint(constraint)));
            }
            // process B in A => B
            for(auto constraint: implication.second)
            { // take the constraints in second as they are
                // check whether the given constraint is one of the input constraints
                unsigned index = 0;
                for( ; index < mConstraints.size(); ++index )
                    if (mConstraints[index] == constraint)
                        break;
                if (mConstraints.size() != index)
                { // the constraint matches the input constraint at position i
                    for (auto i: mConstraintsMap)
                    {
                        if (i.second == index) // found the entry in the constraint map
                        {
                            subformulas.insert(newFormula((*i.first)->pConstraint()));
                            break;
                        }
                    }
                }
                else // add a new constraint
                    subformulas.insert(newFormula(convertConstraint(constraint)));
            }
            Module::addDeduction(newFormula(OR, subformulas));
        }
    }

    /**
     *
     * @param index
     * @return
     */
    inline const Formula* CADModule::getConstraintAt( unsigned index )
    {
        for( ConstraintIndexMap::const_iterator i = mConstraintsMap.begin(); i != mConstraintsMap.end(); ++i )
        {
            if( i->second == index ) // found the entry in the constraint map
                return *i->first;
        }
//        cout << "Constraint index = " << index << " of constraint " << mConstraints[index] << endl;
        assert( false );    // The given index should match an input constraint!
        return NULL;
    }

    /**
     * Increment all indices stored in the constraint map being greater than the given index; decrement if decrement is true.
     * @param index
     * @param decrement
     */
    inline void CADModule::updateConstraintMap( unsigned index, bool decrement )
    {
        if( decrement )
        {
            for( ConstraintIndexMap::iterator i = mConstraintsMap.begin(); i != mConstraintsMap.end(); ++i )
                if( i->second > index )
                    --i->second;
        }
        else
        {
            for( ConstraintIndexMap::iterator i = mConstraintsMap.begin(); i != mConstraintsMap.end(); ++i )
                if( i->second > index )
                    ++i->second;
        }
    }

}    // namespace smtrat

