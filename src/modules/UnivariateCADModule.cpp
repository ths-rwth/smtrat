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
 * @file UnivariateCADModule.cpp
 *
 * @author Ulrich Loup
 * @since 2012-01-19
 * @since 2012-04-09
 */

#include "../Manager.h"
#include "UnivariateCADModule.h"

using GiNaCRA::UnivariatePolynomial;
using GiNaCRA::UnivariatePolynomialSet;
using GiNaCRA::Constraint;
using GiNaCRA::Polynomial;
using GiNaCRA::CAD;
using GiNaCRA::RealAlgebraicPoint;
using GiNaC::sign;
using GiNaC::ZERO_SIGN;
using GiNaC::POSITIVE_SIGN;
using GiNaC::NEGATIVE_SIGN;
using GiNaC::ex_to;

namespace smtrat
{
    UnivariateCADModule::UnivariateCADModule( Manager* const _tsManager, const Formula* const _formula ):
        Module( _tsManager, _formula ),
        mCADs(),
        mCADsToCheck(),
        mSubformulaBuckets(),
        mIsUnknown( false )
    {
        mModuleType = MT_UnivariateCADModule;
        std::cout << mpTSManager->allVariables().size() << std::endl;
        GiNaC::symtab::const_iterator sym = mpTSManager->allVariables().begin();
        while( sym != mpTSManager->allVariables().end() )
        {
            symbol variable = ex_to<symbol>( sym->second );
            mVariables.push_back( variable );
            mCADs[variable] = CAD( UnivariatePolynomialSet(), vector<symbol>( 1, variable ) );
            //            mCADsToCheck[variable]          = false;
            //            mConstraintsBuckets[variable]   = vector<GiNaCRA::Constraint>();
            //std::cout << __func__ << ":" << __LINE__ << std::endl;
            //            mSubformulaBuckets[variable] = set< const Formula* >();
            std::cout << __func__ << ":" << __LINE__ << std::endl;
            ++sym;
            std::cout << __func__ << ":" << __LINE__ << std::endl;
        }
        std::cout << __func__ << ":" << __LINE__ << std::endl;
    }

    UnivariateCADModule::~UnivariateCADModule(){}

    bool UnivariateCADModule::assertSubformula( const Formula* const _formula )
    {
        assert( _formula->getType() == REALCONSTRAINT );
        Module::assertSubFormula( _formula );
        addReceivedSubformulaToPassedFormula( receivedFormulaSize() - 1 );
        // check whether we get a multivariate constraint in which case we do not solve for the constraint
        if( _formula->constraint().variables().size() > 1 )
        {
            mIsUnknown = true;    // set to false again if the unresolvable constraint(s) are removed again due to popBacktrackPoint
            return true;
        }
        symbol variable = ex_to<symbol>( _formula->constraint().variables().begin()->second );
        // find the cad appropriate to the constraint's variable and add the polynomial
        mCADs.find( variable )->second.addPolynomial( UnivariatePolynomial( _formula->constraint().lhs(), variable, false ), mVariables );
        // enable the flag indicating that this cad needs to be checked for consistency
        mCADsToCheck[variable] = true;
        // find the constraint bucket appropriate to the constraint's variable and add the constraint
        mConstraintsBuckets[variable].push_back( convertConstraint( _formula->constraint() ) );
        mSubformulaBuckets[variable].insert( _formula );
        return true;
    }

    Answer UnivariateCADModule::isConsistent()
    {
        if( mIsUnknown )
        {
            return runBackends();
        }
        for( vector<symbol>::const_iterator variable = mVariables.begin(); variable != mVariables.end(); ++variable )
        {    // collect for each variable, which shall be checked for consistency, its constraints
            if( mCADsToCheck[*variable] )
            {
                RealAlgebraicPoint r;
                if( !mCADs[*variable].check( mConstraintsBuckets[*variable], r ) )
                {
                    mInfeasibleSubsets.clear();
                    mInfeasibleSubsets.push_back( mSubformulaBuckets[*variable] );
                    return False;
                }
                else
                    mCADsToCheck[*variable] = false;    // mark checked
            }
        }
        return True;
    }

    void UnivariateCADModule::popBacktrackPoint()
    {
        //TODO: uncomment and bugfix this
        //        vector< const Constraint* > constraintsToRemove = removeAllOriginatedBy( mBackTrackPoints.back() );
        //      
        //      assert( !constraintsToRemove.empty() );

        //        for( vector< const Constraint* >::iterator constraint = constraintsToRemove.begin();
        //           constraint != constraintsToRemove.end();
        //           ++constraint )
        //        {
        //            set< const Formula* > currentSubformulas = mSubformulaBuckets[(*constraint)->variables().begin()->second];
        //            set< const Formula* >::iterator delIter = currentSubformulas.begin();
        //            while( delIter != currentSubformulas.end() )
        //            {
        //              if( (*delIter)->pConstraint() == *constraint )
        //              {
        //                  break;
        //              }
        //              ++delIter;
        //            }
        //            if( delIter != currentSubformulas.end() )
        //            {    // element to erase has been found
        //                currentSubformulas.erase( delIter );
        //                mSubformulaBuckets[(*constraint)->variables().begin()->second] = currentSubformulas;
        //            }
        //        }
    }

    ///////////////////////
    // Auxiliary methods //
    ///////////////////////

    /**
     * Converts the constraint types.
     * @param c constraint of the SMT-RAT
     * @return constraint of GiNaCRA
     */
    const GiNaCRA::Constraint UnivariateCADModule::convertConstraint( const Constraint& c )
    {
        // convert the constraints variables
        vector<symbol> variables = vector<symbol>();
        for( register GiNaC::symtab::const_iterator i = c.variables().begin(); i != c.variables().end(); ++i )
            variables.push_back( ex_to<symbol>( i->second ) );
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
        return GiNaCRA::Constraint( Polynomial( c.lhs() ), signForConstraint, variables, cadConstraintNegated );
    }

}    // namespace smtrat

