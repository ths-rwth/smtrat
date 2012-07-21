/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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
 * @version 2012-07-03
 */

#include "../Manager.h"
#include "CADModule.h"
#include "UnivariateCADModule.h"

#include <ginacra/ginacra.h>

using GiNaCRA::UnivariatePolynomial;
using GiNaCRA::EliminationSet;
using GiNaCRA::Constraint;
using GiNaCRA::Polynomial;
using GiNaCRA::CAD;
using GiNaCRA::RealAlgebraicPoint;
using GiNaCRA::ConflictGraph;
using GiNaCRA::ConflictGraphVertexHasHigherDegree;

using GiNaC::sign;
using GiNaC::ZERO_SIGN;
using GiNaC::POSITIVE_SIGN;
using GiNaC::NEGATIVE_SIGN;
using GiNaC::ex_to;
using GiNaC::is_exactly_a;

using namespace std;

namespace smtrat
{
    CADModule::CADModule( Manager* const _tsManager, const Formula* const _formula ):
        Module( _tsManager, _formula ),
        mCAD(),
        mConstraints(),
        mConstraintsMap(),
        mSatisfiable( true )
    {
        mModuleType = MT_CADModule;
        mInfeasibleSubsets.clear();    // initially everything is satisfied
        //        vector<symbol> variables = vector<symbol>();
        //        for( register GiNaC::symtab::const_iterator sym = mpTSManager->allVariables().begin(); sym != mpTSManager->allVariables().end(); ++sym )
        //            variables.push_back( ex_to<symbol>( sym->second ));
        //        GiNaCRA::CADSettings setting = GiNaCRA::CADSettings::getSettings( );
        //        mCAD = CAD( EliminationSet(), variables, setting );
    }

    CADModule::~CADModule(){}

    bool CADModule::assertSubformula( Formula::const_iterator _subformula )
    {
        assert( (*_subformula)->getType() == REALCONSTRAINT );
        Module::assertSubformula( _subformula );
        vector<symbol> variables = vector<symbol>();
        for( register GiNaC::symtab::const_iterator sym = (*_subformula)->constraint().variables().begin();
                sym != (*_subformula)->constraint().variables().end(); ++sym )
            variables.push_back( ex_to<symbol>( sym->second ) );
        //        addReceivedSubformulaToPassedFormula( receivedFormulaSize() - 1 ); // passed formula not needed since module does not call backends
        // check whether unsatisfiability was determined before and no constrained was removed so far
        if( !mSatisfiable )
            return false;
        // add the constraint to the local list of constraints and memorize the index/constraint assignment if the constraint is not present already
        if( mConstraintsMap.find( _subformula ) != mConstraintsMap.end() )
            return mSatisfiable;    // constraint already considered
        mConstraints.push_back( convertConstraint( (*_subformula)->constraint() ) );
        mConstraintsMap[ _subformula ] = mConstraints.size() - 1;
        // add the polynomial to the cad
        mCAD.addPolynomial( GiNaCRA::UnivariatePolynomial( (*_subformula)->constraint().lhs(), variables.front(), false ), variables );    // false: disable input checks
        // check the extended constraints for satisfiability
        #ifdef MODULE_VERBOSE
        cout << "Checking constraint set " << endl;
        for( auto k = mConstraints.begin(); k != mConstraints.end(); ++k )
            cout << " " << *k << endl;
        cout << "over the variables " << endl;
        vector<symbol> vars = mCAD.variables();
        for( auto k = vars.begin(); k != vars.end(); ++k )
            cout << " " << *k << endl;
        #endif
        GiNaCRA::RealAlgebraicPoint r;
        ConflictGraph               conflictGraph;
        if( !mCAD.check( mConstraints, r, conflictGraph ) )
        {
            vec_set_const_pFormula infeasibleSubsets = extractMinimalInfeasibleSubsets( conflictGraph );
            assert( !infeasibleSubsets.empty() && !infeasibleSubsets.front().empty() );
            for( vec_set_const_pFormula::const_iterator i = infeasibleSubsets.begin(); i != infeasibleSubsets.end(); ++i )
                mInfeasibleSubsets.push_back( *i );
            #ifdef MODULE_VERBOSE
            cout << endl << "#Samples: " << mCAD.samples().size() << endl;
            cout << "Result: false" << endl;
            printInfeasibleSubsets();
            cout << "Performance gain: " << (mpReceivedFormula->size() - mInfeasibleSubsets.front().size()) << endl << endl;
            #endif
            mSatisfiable = false;
            return false;
        }
        #ifdef MODULE_VERBOSE
        cout << endl << "#Samples: " << mCAD.samples().size() << endl;
        cout << "Result: true" << endl << endl;
        #endif
        mInfeasibleSubsets.clear();
        return true;
    }

    Answer CADModule::isConsistent()
    {
        if( mSatisfiable )
            return True;
        return False;
    }

    void CADModule::removeSubformula( Formula::const_iterator _subformula )
    {
        assert( (*_subformula)->getType() == REALCONSTRAINT );
        try
        {
            ConstraintIndexMap::iterator constraintIt = mConstraintsMap.find( _subformula );
            if( constraintIt == mConstraintsMap.end() )
                return; // there is nothing to remove
//            assert( std::find( mpReceivedFormula->begin(), mpReceivedFormula->end(), *_subformula ) == mpReceivedFormula->end() && constraintIt != mConstraintsMap.end() );    // the constraint to be removed should have been asserted before!
            GiNaCRA::Constraint constraint = mConstraints[constraintIt->second];
            unsigned constraintIndex = constraintIt->second;
            // remove the constraint in mConstraintsMap
            mConstraintsMap.erase( constraintIt );
            // reduce the CAD object
            mCAD.removePolynomial( GiNaCRA::UnivariatePolynomial( constraint.polynomial(), constraint.variables().front(), false ) );    // false: disable input checks
            // remove the constraint from the list of constraints
            mConstraints.erase( mConstraints.begin() + constraintIndex );    // erase the (constraintIt->second)-th element
            // update the constraint / index map, i.e., decrement all indices above the removed one
            updateConstraintMap( constraintIndex );
            // forces re-checking the CAD with the next call to assertSubformula
            mSatisfiable = true;
            Module::removeSubformula( _subformula );
        }
        catch( std::out_of_range )
        {
            assert( false );    // the constraint to be removed should have been put to mConstraints before
            return;
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

    inline vec_set_const_pFormula CADModule::extractMinimalInfeasibleSubsets( const ConflictGraph& conflictGraph )
    {
        // create list of vertices sorted by descending degree
        ConflictGraph::Vertices vertices = conflictGraph.vertices();
        vertices.sort( ConflictGraphVertexHasHigherDegree( conflictGraph ) );
        // construct vertex cover by list heuristic
        ConflictGraph::Vertices vertexCover = ConflictGraph::Vertices();    // keep vertexCover sorted
        for( ConflictGraph::vertex_riterator v = vertices.rbegin(); v != vertices.rend(); ++v )
        {
            for( ConflictGraph::vertex_iterator n = conflictGraph.neighbors( *v ).begin(); n != conflictGraph.neighbors( *v ).end(); ++n )
            {
                if( *n >= *v )
                {    // n is right of v
                    ConflictGraph::Vertices::iterator position = std::lower_bound( vertexCover.begin(), vertexCover.end(), *n );
                    if( position == vertexCover.end() || *position != *n )
                    {    // *n not in the vertex cover, yet => add the vertex in a sorted way and continue with the next vertex
                        vertexCover.insert( position, *n );
                        break;
                    }
                }
            }
        }
        // collect constraints according to the vertex cover
        vec_set_const_pFormula mis = vec_set_const_pFormula( 1, std::set<const Formula*>() );
        mis.front().insert( getConstraintAt( mConstraints.size() - 1 ) );    // the last constraint is assumed to be always in the MIS
        for( ConflictGraph::vertex_iterator v = vertexCover.begin(); v != vertexCover.end(); ++v )
            mis.front().insert( getConstraintAt( *v ) );
        return mis;
    }

    inline const Formula* CADModule::getConstraintAt( unsigned index )
    {
        for( ConstraintIndexMap::const_iterator i = mConstraintsMap.begin(); i != mConstraintsMap.end(); ++i )
        {
            if( i->second == index ) // found the entry in the constraint map
                return *i->first;
        }
        cout << "Constraint index = " << index << " of constraint " << mConstraints[index] << endl;
        assert( false );    // The given index should match an input constraint!
    }

    inline void CADModule::updateConstraintMap( unsigned index, bool decrement )
    {
        for( ConstraintIndexMap::iterator i = mConstraintsMap.begin(); i != mConstraintsMap.end(); ++i )
            if( i->second > index )
                i->second = decrement ? i->second - 1 : i->second + 1;
    }

}    // namespace smtrat

