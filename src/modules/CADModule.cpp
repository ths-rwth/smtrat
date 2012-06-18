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
 * @version 2012-06-07
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
using GiNaC::sign;
using GiNaC::ZERO_SIGN;
using GiNaC::POSITIVE_SIGN;
using GiNaC::NEGATIVE_SIGN;
using GiNaC::ex_to;
using namespace std;

namespace smtrat
{
    CADModule::CADModule( Manager* const _tsManager, const Formula* const _formula ):
        Module( _tsManager, _formula ),
        mCAD(),
        mConstraints()
    {
        this->mModuleType = MT_CADModule;
        vector<symbol> variables = vector<symbol>();
        for( register GiNaC::symtab::const_iterator sym = Formula::mConstraintPool.variables().begin(); sym != Formula::mConstraintPool.variables().end(); ++sym )
            variables.push_back( ex_to<symbol>( sym->second ));
        GiNaCRA::CADSettings setting = GiNaCRA::CADSettings::getSettings( );
        mCAD = CAD( EliminationSet(), variables, setting );
    }

    CADModule::~CADModule(){}

    bool CADModule::assertSubFormula( const Formula* const _formula )
    {
        vector<symbol> variables = vector<symbol>();
        for( register GiNaC::symtab::const_iterator sym = _formula->constraint().variables().begin(); sym != _formula->constraint().variables().end();
                ++sym )
            variables.push_back( ex_to<symbol>( sym->second ));
        assert( _formula->getType() == REALCONSTRAINT );
        Module::assertSubFormula( _formula );
        addReceivedSubformulaToPassedFormula( receivedFormulaSize() - 1 );
        // add the polynomial to the cad
        mCAD.addPolynomial( UnivariatePolynomial( _formula->constraint().lhs(), variables.front(), false ), variables );    // false: disable input checks
        // find the constraint bucket appropriate to the constraint's variable and add the constraint
        mConstraints.push_back( convertConstraint( _formula->constraint() ));
        return true;
    }

    Answer CADModule::isConsistent()
    {
        cout << "Check constraint set " << endl;

        for( auto k = mConstraints.begin(); k != mConstraints.end(); ++k )
            cout << " " << *k << endl;
        vector<symbol> variables = mCAD.variables();
        cout << "over the variables " << endl;
        for( auto k = variables.begin(); k != variables.end(); ++k )
            cout << " " << *k << endl;
        RealAlgebraicPoint r;
        if( !mCAD.check( mConstraints, r ))
        {
            mInfeasibleSubsets.clear();

            /*
             * Set the infeasible subset to the set of all received constraints.
             */
            set<const Formula*> infeasibleSubset = set<const Formula*>();
            for( Formula::const_iterator cons = receivedFormulaBegin(); cons != receivedFormulaEnd(); ++cons )
                infeasibleSubset.insert( *cons );
            mInfeasibleSubsets.push_back( infeasibleSubset );
            cout << "#Samples: " << mCAD.samples().size() << endl;
            cout << "Result: false" << endl;
            printInfeasibleSubsets();
            return False;
        }
        cout << "Result: true" << endl;
        return True;
    }

    void CADModule::popBacktrackPoint()
    {
        signed upperBound = receivedFormulaSize();
        Module::popBacktrackPoint();
        // remove each constraint in the backtracked range from the local constraint list, and remove the respective polynomials from the CAD
        for( signed pos = lastBacktrackpointsEnd() + 1; pos < upperBound; ++pos )
        {
            GiNaCRA::Constraint                   constraint     = convertConstraint( receivedFormulaAt( pos )->constraint() );
            vector<GiNaCRA::Constraint>::iterator constraintIter = find( mConstraints.begin(), mConstraints.end(), constraint );
            assert( constraintIter != mConstraints.end() );
            mCAD.removePolynomial( UnivariatePolynomial( constraintIter->polynomial(), constraintIter->variables().front() ) );
            mConstraints.erase( constraintIter );
        }
//        /// recompute the CAD projection for the remaining polynomials (@todo: use incremental remove operation instead)
//        symbol mainVariable = mCAD.variables().front();
//        EliminationSet polynomials = EliminationSet();
//        for( vector<GiNaCRA::Constraint>::const_iterator constraint = mConstraints.begin(); constraint != mConstraints.end(); ++constraint )
//            polynomials.insert( UnivariatePolynomial( constraint->polynomial(), mainVariable ) );
//        GiNaCRA::CADSettings setting = GiNaCRA::CADSettings::getSettings( GiNaCRA::ODDDEG_CADSETTING | GiNaCRA::EAGERLIFTING_CADSETTING );
//        mCAD = CAD( polynomials, mCAD.variables(), setting );
    }

    ///////////////////////
    // Auxiliary methods //
    ///////////////////////

    /**
     * Converts the constraint types.
     * @param c constraint of the SMT-RAT
     * @return constraint of GiNaCRA
     */
    const GiNaCRA::Constraint CADModule::convertConstraint( const Constraint& c )
    {
        //        // convert the constraints variables
        //        vector<symbol> variables = vector<symbol>();
        //        for( register GiNaC::symtab::const_iterator i = c.variables().begin(); i != c.variables().end(); ++i )
        //            variables.push_back( ex_to<symbol>( i->second ));
        register sign signForConstraint    = ZERO_SIGN;
        register bool cadConstraintNegated = false;
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
                assert( false == true );
            }
        }
        return GiNaCRA::Constraint( Polynomial( c.lhs() ), signForConstraint, mCAD.variables(), cadConstraintNegated );
    }

}    // namespace smtrat

