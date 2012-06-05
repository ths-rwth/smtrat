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

/*
 * File:   PreProModule.cpp
 * Author: Dennis Scully
 *
 * Created on 23. April 2012, 14:53
 */

#include "../Manager.h"
#include "PreProModule.h"

using namespace std;
using namespace GiNaC;

namespace smtrat
{
    /**
     * Constructor
     */
    PreProModule::PreProModule( Manager* const _tsManager, const Formula* const _formula ):
        Module( _tsManager, _formula ),
        mFreshConstraintReceived( false ),
        mNumberOfComparedConstraints( 0 ),
        mNumberOfAddedSubformulas( 0 ),
        mReceivedConstraints( std::vector<const Constraint* >() ),
        mConstraintOrigins( std::vector<const Formula* >() ),
        mConstraintBacktrackPoints( std::vector<unsigned>() )
    {
        this->mModuleType = MT_PreProModule;
    }

    /**
     * Destructor:
     */
    PreProModule::~PreProModule(){}

    /**
     * Methods:
     */

    /**
     * Adds a constraint to this modul.
     *
     * @param _constraint The constraint to add to the already added constraints.
     *
     * @return  true,   if the constraint and all previously added constraints are consistent;
     *          false,  if the added constraint or one of the previously added ones is inconsistent.
     */
    bool PreProModule::assertSubFormula( const Formula* const _formula )
    {
        _formula->FormulaToConstraints( mReceivedConstraints );
        while( mReceivedConstraints.size() <= mConstraintOrigins.size() )
        {
            mConstraintOrigins.push_back( _formula );
        }
        mFreshConstraintReceived = true;
        return true;
    }

    /**
     * Checks the so far received constraints for consistency.
     *
     * @return  True,    if the conjunction of received constraints is consistent;
     *          False,   if the conjunction of received constraints is inconsistent;
     *          Unknown, otherwise.
     */
    Answer PreProModule::isConsistent()
    {
        if( mFreshConstraintReceived == true )
        {
            for( unsigned i = mNumberOfAddedSubformulas; i < receivedFormulaSize(); ++i )
            {
                addReceivedSubformulaToPassedFormula( i );
            }
            for( unsigned posConsA = mNumberOfComparedConstraints; posConsA < mReceivedConstraints.size(); posConsA++ )
            {
                const Constraint* tempConstraintA = mReceivedConstraints.at( posConsA );
                mNumberOfComparedConstraints++;
                for( unsigned posConsB = 0; posConsB < posConsA; posConsB++)
                {
                    const Constraint* tempConstraintB = mReceivedConstraints.at( posConsB );
                    switch( Constraint::compare( *tempConstraintA, *tempConstraintB ) )
                    {
                        Formula* _tSubformula;
                        case 2: // A IFF B
                        {
                            _tSubformula = new Formula( IFF );
                            _tSubformula->addSubformula( new Formula( tempConstraintA ) );
                            _tSubformula->addSubformula( new Formula( tempConstraintB ) );
                            break;
                        }
                        case 1: // A => B
                        {
                            _tSubformula = new Formula( IMPLIES );
                            _tSubformula->addSubformula( new Formula( tempConstraintA ) );
                            _tSubformula->addSubformula( new Formula( tempConstraintB ) );
                            break;
                        }

                        case -1: // B => A
                        {
                            _tSubformula = new Formula( IMPLIES );
                            _tSubformula->addSubformula( new Formula( tempConstraintB ) );
                            _tSubformula->addSubformula( new Formula( tempConstraintA ) );
                            break;
                        }
                        case -2: // A XOR B
                        {
                            _tSubformula = new Formula( XOR );
                            _tSubformula->addSubformula( new Formula( tempConstraintA ) );
                            _tSubformula->addSubformula( new Formula( tempConstraintB ) );
                            break;
                        }
                        default:
                        {
                            break;
                        }
                        // Create Origins
                        std::set< const Formula* > originset;
                        originset.insert( mConstraintOrigins.at( posConsA ) );
                        originset.insert( mConstraintOrigins.at( posConsB ) );
                        vec_set_const_pFormula origins = vec_set_const_pFormula();
                        origins.push_back( originset );
                        // Add learned Subformula and Origins to PassedFormula
                        addSubformulaToPassedFormula( _tSubformula, origins );
                    }
                }
            }
            mFreshConstraintReceived = false;
        }
        return True;
    }

     /**
     * Pushs a backtrackpoint, to the stack of backtrackpoints.
     */
    void PreProModule::pushBacktrackPoint()
    {
        mConstraintBacktrackPoints.push_back( mReceivedConstraints.size() );
    }

    /**
     * Pops the last backtrackpoint, from the stack of backtrackpoints.
     */
    void PreProModule::popBacktrackPoint()
    {
        while( mReceivedConstraints.size() > mConstraintBacktrackPoints.back() )
        {
            mReceivedConstraints.pop_back();
        }
        mConstraintBacktrackPoints.pop_back();
        Module::popBacktrackPoint();
    }
}    // namespace smtrat

