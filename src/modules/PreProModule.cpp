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
        mReceivedConstraints( std::vector<const Constraint* >() ),
        mConstraintOrigins( std::vector<const Formula* >() ),
        mConstraintBacktrackPoints( std::vector< pair< pair< bool, unsigned >, pair< unsigned, unsigned > > >() )
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
    bool PreProModule::assertSubformula( Formula::const_iterator _subformula )
    {
        Module::assertSubformula( _subformula );
        addReceivedSubformulaToPassedFormula( _subformula );
        (*_subformula)->FormulaToConstraints( mReceivedConstraints );
        while( mReceivedConstraints.size() > mConstraintOrigins.size() )
        {
            mConstraintOrigins.push_back( *_subformula );
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
        string str_out = "";
//        cout << endl << "Before isConsistent:" << endl << endl;
//        this->pPassedFormula()->print(cout, str_out, true);
//        cout << endl;

        if( mFreshConstraintReceived == true )
        {
            for( unsigned posConsA = mNumberOfComparedConstraints; posConsA < mReceivedConstraints.size(); ++posConsA )
            {

                const Constraint* tempConstraintA = mReceivedConstraints.at( posConsA );
                mNumberOfComparedConstraints++;
                for( unsigned posConsB = 0; posConsB < posConsA; ++posConsB )
                {
                    const Constraint* tempConstraintB = mReceivedConstraints.at( posConsB );
                    Formula* _tSubformula = NULL;
                    switch( Constraint::compare( *tempConstraintA, *tempConstraintB ) )
                    {

                        /*case 2: // A IFF B
                        {
                            _tSubformula = new Formula( IFF );
                            _tSubformula->addSubformula( new Formula( tempConstraintA ) );
                            _tSubformula->addSubformula( new Formula( tempConstraintB ) );
                            break;
                        }*/
                        case 1: // not A or B
                        {
                            _tSubformula = new Formula( OR );
                            Formula* tmpFormula = new Formula( NOT );
                            tmpFormula->addSubformula( new Formula( tempConstraintA ) );
                            _tSubformula->addSubformula( tmpFormula );
                            _tSubformula->addSubformula( new Formula( tempConstraintB ) );
                            break;
                        }

                        case -1: // not B or A
                        {
                            _tSubformula = new Formula( OR );
                            Formula* tmpFormula = new Formula( NOT );
                            tmpFormula->addSubformula( new Formula( tempConstraintB ) );
                            _tSubformula->addSubformula( tmpFormula );
                            _tSubformula->addSubformula( new Formula( tempConstraintA ) );
                            break;
                        }
                        case -2: // not A or not B
                        {
                            _tSubformula = new Formula( OR );
                            Formula* tmpFormulaA = new Formula( NOT );
                            tmpFormulaA->addSubformula( new Formula( tempConstraintA ) );
                            Formula* tmpFormulaB = new Formula( NOT );
                            tmpFormulaB->addSubformula( new Formula( tempConstraintB ) );
                            _tSubformula->addSubformula( tmpFormulaA );
                            _tSubformula->addSubformula( tmpFormulaB );
                            break;
                        }
                        default:
                        {
                            break;
                        }
                    }
                    if( _tSubformula != NULL )
                    {
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
//        cout << endl << "After isConsistent:" << endl << endl;
//        this->pPassedFormula()->print(cout, str_out, true);
//        cout << endl;

		Answer a = runBackends();

        if( a == False )
        {
            getInfeasibleSubsets();
        }

        return a;
    }

    /**
     * Removes a everything related to a sub formula of the received formula.
     *
     * @param _subformula The sub formula of the received formula to remove.
     */
    void PreProModule::removeSubformula( Formula::const_iterator _subformula )
    {
        // TODO: Adapt the code of the previous methods pushBacktrackPoint and
        //       popbacktrackpoint such that it is applied here.

//        PreProModule::pushBacktrackPoint()
//        {
//            Module::pushBacktrackPoint();
//            pair< bool, unsigned > firstpair( mFreshConstraintReceived, mNumberOfComparedConstraints );
//            pair< unsigned, unsigned > secondpair( pPassedFormula()->size(), mReceivedConstraints.size() );
//            pair< pair< bool, unsigned >, pair< unsigned, unsigned > > newbacktrack( firstpair, secondpair );
//            mConstraintBacktrackPoints.push_back( newbacktrack );
//        }
//        PreProModule::popBacktrackPoint()
//        {
//            mFreshConstraintReceived = mConstraintBacktrackPoints.back().first.first;
//            mNumberOfComparedConstraints = mConstraintBacktrackPoints.back().first.second;
//            while( mConstraintBacktrackPoints.back().second.first != pPassedFormula()->size() )
//            {
//                removeSubformulaFromPassedFormula( pPassedFormula()->size()-1 );
//            }
//            while( mReceivedConstraints.size() != mConstraintBacktrackPoints.back().second.second )
//            {
//                mReceivedConstraints.pop_back();
//                mConstraintOrigins.pop_back();
//            }
//            mConstraintBacktrackPoints.pop_back();
//            Module::popBacktrackPoint();
//        }
    }
}    // namespace smtrat

