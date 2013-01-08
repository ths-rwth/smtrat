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
 * @version 2012-12-14
 */

//#define MODULE_VERBOSE

#include "../Manager.h"
#include "CADModule.h"

#include <ginacra/ginacra.h>
#include <ginacra/Constraint.h>
#include <iostream>

using GiNaCRA::UnivariatePolynomial;
using GiNaCRA::EliminationSet;
using GiNaCRA::Constraint;
using GiNaCRA::Polynomial;
using GiNaCRA::CAD;
using GiNaCRA::RealAlgebraicPoint;
using GiNaCRA::ConflictGraph;

using GiNaC::sign;
using GiNaC::ZERO_SIGN;
using GiNaC::POSITIVE_SIGN;
using GiNaC::NEGATIVE_SIGN;
using GiNaC::ex_to;
using GiNaC::is_exactly_a;

using namespace std;

// CAD settings
//#define SMTRAT_CAD_ALTERNATIVE_SETTING
//#define SMTRAT_CAD_DISABLEEQUATIONDETECT_SETTING
//#define SMTRAT_CAD_GENERIC_SETTING
//#define SMTRAT_CAD_DISABLE_SMT
//#define SMTRAT_CAD_DISABLE_THEORYPROPAGATION
#define SMTRAT_CAD_DISABLE_MIS

#ifdef SMTRAT_CAD_DISABLE_SMT
    #define SMTRAT_CAD_DISABLE_THEORYPROPAGATION
    #define SMTRAT_CAD_DISABLE_MIS
#endif

namespace smtrat
{
    CADModule::CADModule( const Formula* const _formula, Manager* const _tsManager ):
        Module( _formula, _tsManager ),
        mCAD(),
        mConstraints(),
        mConstraintsMap(),
        mRealAlgebraicSolution()
        #ifdef CAD_USE_VARIABLE_BOUNDS
        ,
        mVariableBounds()
        #endif
    {
        mModuleType = MT_CADModule;
        mInfeasibleSubsets.clear();    // initially everything is satisfied
        // CAD setting
        GiNaCRA::CADSettings setting = mCAD.setting();
        setting.autoEliminate = false;
        #ifdef CAD_USE_VARIABLE_BOUNDS
        setting.simplifyEliminationByBounds = true;
        setting.earlyLiftingPruningByBounds = true;
        #endif
        // general setting set
        #ifdef SMTRAT_CAD_ALTERNATIVE_SETTING
            setting = GiNaCRA::CADSettings::getSettings( GiNaCRA::RATIONALSAMPLE_CADSETTING );
            setting.autoEliminate = false;
        #else
            #ifdef SMTRAT_CAD_DISABLEEQUATIONDETECT_SETTING
                setting = GiNaCRA::CADSettings::getSettings( GiNaCRA::GENERIC_CADSETTING );
                setting.autoEliminate = false;
            #else
                setting = GiNaCRA::CADSettings::getSettings( GiNaCRA::EQUATIONDETECT_CADSETTING ); // standard
                setting.autoEliminate = false;
                setting.warmRestart = true;
                setting.simplifyByFactorization = true;
                setting.simplifyByRootcounting= true;
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
        mCAD.alterSetting( setting );
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
    bool CADModule::assertSubformula( Formula::const_iterator _subformula )
    {
        assert( (*_subformula)->getType() == REALCONSTRAINT );
        Module::assertSubformula( _subformula );

        #ifdef CAD_USE_VARIABLE_BOUNDS
        if( !mVariableBounds.addBound( (*_subformula)->pConstraint(), *_subformula ) )
        {
        #endif

        if( mSolverState == False )
            return false;
        // add the constraint to the local list of constraints and memorize the index/constraint assignment if the constraint is not present already
        if( mConstraintsMap.find( _subformula ) != mConstraintsMap.end() )
            return true;    // the exact constraint was already considered
        GiNaCRA::Constraint constraint = convertConstraint( (*_subformula)->constraint() );
        mConstraints.push_back( constraint );
        mConstraintsMap[ _subformula ] = mConstraints.size() - 1;
        mCAD.addPolynomial( constraint.polynomial(), constraint.variables() );
        #ifdef CAD_USE_VARIABLE_BOUNDS
        }
        #endif
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
        if( !mInfeasibleSubsets.empty() )
            return False; // there was no constraint removed which was in a previously generated infeasible subset
        #ifdef MODULE_VERBOSE
        cout << "Checking constraint set " << endl;
        for( vector<GiNaCRA::Constraint>::const_iterator k = mConstraints.begin(); k != mConstraints.end(); ++k )
            cout << " " << *k << endl;
        #endif
        // perform the scheduled elimination and see if there were new variables added
        mCAD.prepareElimination();
        #ifdef MODULE_VERBOSE
        cout << "over the variables " << endl;
        vector<symbol> vars = mCAD.variables();
        for( vector<GiNaC::symbol>::const_iterator k = vars.begin(); k != vars.end(); ++k )
            cout << " " << *k << endl;
        #endif
        // check the extended constraints for satisfiability
        #ifdef CAD_USE_VARIABLE_BOUNDS
        if( variableBounds().isConflicting() )
        {
            mInfeasibleSubsets.push_back( variableBounds().getConflict() );
            mSolverState = False;
            mRealAlgebraicSolution = GiNaCRA::RealAlgebraicPoint();
            return False;
        }
        GiNaCRA::BoundMap boundMap = GiNaCRA::BoundMap();
        GiNaCRA::evalintervalmap eiMap = mVariableBounds.getEvalIntervalMap();
        for( auto iter = eiMap.begin(); iter != eiMap.end(); ++iter )
        {
            unsigned pos = mCAD.variable( iter->first );
            assert( boundMap.find( pos ) == boundMap.end() );
            boundMap[pos] = iter->second;
        }
        #endif
        ConflictGraph conflictGraph;
        list<pair<list<GiNaCRA::Constraint>, list<GiNaCRA::Constraint> > > deductions;
        if( !mCAD.check( mConstraints, mRealAlgebraicSolution, conflictGraph, boundMap, deductions, false, false ) )
        {
            #ifdef SMTRAT_CAD_DISABLE_SMT
            // simulate non-incrementality by constructing a trivial infeasible subset and clearing all data in the CAD
            #define SMTRAT_CAD_DISABLE_MIS // this constructs a trivial infeasible subset below
            #define SMTRAT_CAD_DISABLE_THEORYPROPAGATION // no lemmata from staisfying assignments are going to be constracted
            mCAD.clear();
            // replay adding the polynomials as scheduled polynomials
            for( vector<GiNaCRA::Constraint>::const_iterator constraint = mConstraints.begin(); constraint != mConstraints.end(); ++constraint )
                mCAD.addPolynomial( constraint->polynomial(), constraint->variables() );
            #endif
            #ifdef SMTRAT_CAD_DISABLE_MIS
            // construct a trivial infeasible subset
            mInfeasibleSubsets.push_back( set<const Formula*>() );
            for( ConstraintIndexMap::const_iterator i = mConstraintsMap.begin(); i != mConstraintsMap.end(); ++i )
                mInfeasibleSubsets.back().insert( *i->first );
            #else
            // construct an infeasible subset
            assert( mCAD.setting().computeConflictGraph );
            #ifdef MODULE_VERBOSE
            cout << "Constructing a minimal infeasible set from the ";
            cout << "conflict graph: " << endl << conflictGraph << endl << endl;
            #endif
            vec_set_const_pFormula infeasibleSubsets = extractMinimalInfeasibleSubsets_GreedyHeuristics( conflictGraph );
            for( vec_set_const_pFormula::const_iterator i = infeasibleSubsets.begin(); i != infeasibleSubsets.end(); ++i )
                mInfeasibleSubsets.push_back( *i );
            #endif
            #ifdef MODULE_VERBOSE
            cout << endl << "#Samples: " << mCAD.samples().size() << endl;
            cout << "Elimination sets:" << endl;
            vector<EliminationSet> elimSets = mCAD.eliminationSets();
            for( unsigned i = 0; i != elimSets.size(); ++i )
                cout << "  Level " << i << " (" << elimSets[i].size() << "): " << elimSets[i] << endl;
            cout << "Result: false" << endl;
            cout << "CAD complete: " << mCAD.isComplete() << endl;
            printInfeasibleSubsets();
            cout << "Performance gain: " << (mpReceivedFormula->size() - mInfeasibleSubsets.front().size()) << endl << endl;
//            mCAD.printSampleTree();
            #endif
            mSolverState = False;
            mRealAlgebraicSolution = GiNaCRA::RealAlgebraicPoint();
            return False;
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
        mSolverState = True;
        return True;
    }

    void CADModule::removeSubformula( Formula::const_iterator _subformula )
    {
        assert( (*_subformula)->getType() == REALCONSTRAINT );
        #ifdef CAD_USE_VARIABLE_BOUNDS
        if( mVariableBounds.removeBound( (*_subformula)->pConstraint(), *_subformula ) == 0 )
        {
        #endif
        try
        {
            ConstraintIndexMap::iterator constraintIt = mConstraintsMap.find( _subformula );
            if( constraintIt == mConstraintsMap.end() )
                return; // there is nothing to remove
            GiNaCRA::Constraint constraint = mConstraints[constraintIt->second];
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
            // update the constraint / index map, i.e., decrement all indices above the removed one
            updateConstraintMap( constraintIndex );
            // remove the constraint from the list of constraints
            mConstraints.erase( mConstraints.begin() + constraintIndex );    // erase the (constraintIt->second)-th element
            // remove the corresponding polynomial if it is not occurring in another constraint
            bool doDelete = true;
            for( vector<GiNaCRA::Constraint>::const_reverse_iterator c = mConstraints.rbegin(); c != mConstraints.rend(); ++c )
            {
                if( constraint.polynomial() == c->polynomial() )
                {
                    doDelete = false;
                    break;
                }
            }
            if( doDelete ) // no other constraint claims the polynomial, hence remove it from the list and the cad
                mCAD.removePolynomial( constraint.polynomial() );
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
            // forces complete re-checking of all samples in the CAD with the next call to CAD::check
            Module::removeSubformula( _subformula );
        }
        catch( std::out_of_range )
        {
            assert( false );    // the constraint to be removed should have been put to mConstraints before
            return;
        }
        #ifdef CAD_USE_VARIABLE_BOUNDS
        }
        #endif
    }

    /**
     * Updates the model.
     */
    void CADModule::updateModel()
    {
        mModel.clear();
        if( mSolverState == True )
        {
            for( unsigned varID = 0; varID < mCAD.variables().size(); ++varID )
            {
                stringstream outA;
                outA << mCAD.variables()[varID];
                stringstream outB;
                GiNaCRA::RealAlgebraicNumberIRPtr irA = std::dynamic_pointer_cast<GiNaCRA::RealAlgebraicNumberIR>( mRealAlgebraicSolution[varID] );
                GiNaCRA::RealAlgebraicNumberNRPtr nrA = std::dynamic_pointer_cast<GiNaCRA::RealAlgebraicNumberNR>( mRealAlgebraicSolution[varID] );
                if( irA != 0 )
                    outB << "zero( " << irA->polynomial() << ", " << irA->order() << " )";
                else if( nrA != 0 )
                    outB << static_cast<GiNaCRA::RealAlgebraicNumberNR>(*nrA);
                else
                    outB << "NaN";
                mModel.insert( pair< const string, string >( outA.str(), outB.str() ) );
            }
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
    inline const GiNaCRA::Constraint CADModule::convertConstraint( const smtrat::Constraint& c )
    {
        // convert the constraints variable
        vector<symbol> variables = vector<symbol>();
        for( GiNaC::symtab::const_iterator i = c.variables().begin(); i != c.variables().end(); ++i )
        {
            assert( is_exactly_a<symbol>( i->second ) );
            variables.push_back( ex_to<symbol>( i->second ) );
        }
        sign signForConstraint = ZERO_SIGN;
        bool cadConstraintNegated = false;
        switch( c.relation() )
        {
            case CR_EQ:
            {
                break;
            }
            case CR_LEQ:
            {
                signForConstraint    = POSITIVE_SIGN;
                cadConstraintNegated = true;
                break;
            }
            case CR_GEQ:
            {
                signForConstraint    = NEGATIVE_SIGN;
                cadConstraintNegated = true;
                break;
            }
            case CR_LESS:
            {
                signForConstraint = NEGATIVE_SIGN;
                break;
            }
            case CR_GREATER:
            {
                signForConstraint = POSITIVE_SIGN;
                break;
            }
            case CR_NEQ:
            {
                cadConstraintNegated = true;
                break;
            }
            default:
            {
                assert( false );
            }
        }
        return GiNaCRA::Constraint( Polynomial( c.lhs() ), signForConstraint, variables, cadConstraintNegated );
    }

    /**
     * Converts the constraint types.
     * @param c constraint of the GiNaCRA
     * @return constraint of SMT-RAT
     */
    inline const Constraint* CADModule::convertConstraint( const GiNaCRA::Constraint& c )
    {
        Constraint_Relation relation = CR_EQ;
        switch( c.sign() )
        {
            case POSITIVE_SIGN:
            {
                if( c.negated() )
                    relation = CR_LEQ;
                else
                    relation = CR_GREATER;
                break;
            }
            case ZERO_SIGN:
            {
                if( c.negated() )
                    relation = CR_NEQ;
                else
                    relation = CR_EQ;
                break;
            }
            case NEGATIVE_SIGN:
            {
                if( c.negated() )
                    relation = CR_GEQ;
                else
                    relation = CR_LESS;
                break;
            }
            default:
            {
                assert( false );
            }
        }
        GiNaC::symtab variables = GiNaC::symtab();
        for( auto i = c.variables().begin(); i != c.variables().end(); ++i )
        {
            stringstream out;
            out << *i;
            variables.insert( pair< string, GiNaC::ex>( out.str(), *i ) );
        }
        return Formula::newConstraint( c.polynomial(), relation, variables );
    }

    /**
     * Computes an infeasible subset of the current set of constraints by approximating a vertex cover of the given conflict graph.
     *
     * Heuristics:
     * Select the highest-degree vertex for the vertex cover and remove it as long as we have edges in the graph.
     *
     * @param conflictGraph
     * @return an infeasible subset of the current set of constraints
     */
    inline vec_set_const_pFormula CADModule::extractMinimalInfeasibleSubsets_GreedyHeuristics( ConflictGraph conflictGraph )
    {
        // initialize MIS with the last constraint
        vec_set_const_pFormula mis = vec_set_const_pFormula( 1, std::set<const Formula*>() );
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
                conflictGraph.removeAdjacentVertices( vertex );
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

    void CADModule::addDeductions( const list<pair<list<GiNaCRA::Constraint>, list<GiNaCRA::Constraint> > >& deductions )
    {
        for( list<pair<list<GiNaCRA::Constraint>, list<GiNaCRA::Constraint> > >::const_iterator implication = deductions.begin(); implication != deductions.end(); ++implication )
        {
            assert( ( !implication->first.empty() && !implication->second.empty() ) || implication->first.size() > 1 || implication->second.size() > 1  );
            Formula* deduction = new Formula( OR );
            // process A in A => B
            for( list<GiNaCRA::Constraint>::const_iterator constraint = implication->first.begin(); constraint != implication->first.end(); ++constraint )
            { // negate all constraints in first
                deduction->addSubformula( new Formula( NOT ) );
                // check whether the given constraint is one of the input constraints
                unsigned index = 0;
                for( ; index < mConstraints.size(); ++index )
                    if( mConstraints[index] == *constraint )
                        break;
                if( mConstraints.size() != index )
                { // the constraint matches the input constraint at position i
                    for( ConstraintIndexMap::const_iterator i = mConstraintsMap.begin(); i != mConstraintsMap.end(); ++i )
                    {
                        if( i->second == index ) // found the entry in the constraint map
                        {
                            deduction->back()->addSubformula( (*i->first)->pConstraint() );
                            break;
                        }
                    }
                }
                else // add a new constraint
                    deduction->back()->addSubformula( convertConstraint( *constraint ) );
            }
            // process B in A => B
            for( list<GiNaCRA::Constraint>::const_iterator constraint = implication->second.begin(); constraint != implication->second.end(); ++constraint )
            { // take the constraints in second as they are
                // check whether the given constraint is one of the input constraints
                unsigned index = 0;
                for( ; index < mConstraints.size(); ++index )
                    if( mConstraints[index] == *constraint )
                        break;
                if( mConstraints.size() != index )
                { // the constraint matches the input constraint at position i
                    for( ConstraintIndexMap::const_iterator i = mConstraintsMap.begin(); i != mConstraintsMap.end(); ++i )
                    {
                        if( i->second == index ) // found the entry in the constraint map
                        {
                            deduction->addSubformula( (*i->first)->pConstraint() );
                            break;
                        }
                    }
                }
                else // add a new constraint
                    deduction->addSubformula( convertConstraint( *constraint ) );
            }
            Module::addDeduction( deduction );
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
     *
     * @param index
     * @param decrement
     */
    inline void CADModule::updateConstraintMap( unsigned index, bool decrement )
    {
        for( ConstraintIndexMap::iterator i = mConstraintsMap.begin(); i != mConstraintsMap.end(); ++i )
            if( i->second > index )
                i->second = decrement ? i->second - 1 : i->second + 1;
    }

}    // namespace smtrat

