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
 * File:   LRAModule.cpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * Created on January 18, 2012, 3:51 PM
 */

#include "LRAModule.h"
#include "../NRATSolver.h"

using namespace std;
using namespace lra;

namespace smtrat
{
    /**
     * Constructor
     */
    LRAModule::LRAModule( Manager* const _tsManager, const Formula* const _formula ):
        Module( _tsManager, _formula )
    {
        this->mModuleType             = MT_LRAModule;
        mNumAddedNonlinearConstraints = 0;
        mLRASolverConstraints         = cons_to_cons_bool_pair_vec_map();
        mpLRASolver                   = new LRASolverA();
    }

    /**
     * Destructor:
     */
    LRAModule::~LRAModule()
    {
        while( !mLRASolverConstraints.empty() )
        {
            while( !mLRASolverConstraints.begin()->second.empty() )
            {
                const Constraint* pConstraint = mLRASolverConstraints.begin()->second.back().first;
                mLRASolverConstraints.begin()->second.pop_back();
                delete pConstraint;
            }
            mLRASolverConstraints.erase( mLRASolverConstraints.begin() );
        }
        delete mpLRASolver;
    }

    /**
     * Methods:
     */

    /**
     * Informs about a new constraints.
     * @param c A new constraint
     *
     */
    bool LRAModule::inform( const Constraint* const _constraint )
    {
        // create constraint adequate for the lrasolver
        cons_to_cons_bool_pair_vec_map::const_iterator iter = addConstraintToLRASolverConstraints( _constraint );

        // inform the lrasolver about the created constraints
        for( cons_bool_pair_vec::const_iterator cbPair = iter->second.begin(); cbPair != iter->second.end(); ++cbPair )
        {
            mpLRASolver->informA( cbPair->first );
        }
        return true;
    }

    /**
     * Adds a constraint to this modul.
     *
     * @param _constraint The constraint to add to the already added constraints.
     *
     * @return  true,   if the constraint and all previously added constraints are consistent;
     *          false,  if the added constraint or one of the previously added ones is inconsistent.
     */
    bool LRAModule::assertSubFormula( const Formula* const _formula )
    {
        assert( _formula->getType() == REALCONSTRAINT );
        Module::assertSubFormula( _formula );
        // add the lrasolver adequate constraints
        cons_to_cons_bool_pair_vec_map::const_iterator iter = addConstraintToLRASolverConstraints( _formula->pConstraint() );

        //inform the lrasolver about the created constraints
        if( iter->second.empty() )
        {
            ++mNumAddedNonlinearConstraints;
        }
        for( cons_bool_pair_vec::const_iterator cbPair = iter->second.begin(); cbPair != iter->second.end(); ++cbPair )
        {
            assert( cbPair->first->relation() != CR_EQ || cbPair->second );
            if( !mpLRASolver->assertLitA( cbPair->first, cbPair->second ) )
            {
                vector<const Constraint*> explanation = mpLRASolver->getExplanation();
                mInfeasibleSubsets.clear();
                mInfeasibleSubsets.push_back( set<const Formula*>() );
                for( Formula::const_iterator subFormula = receivedFormulaBegin(); subFormula != receivedFormulaEnd(); ++subFormula )
                {
                    assert( (*subFormula)->getType() == REALCONSTRAINT );
                    if( find( explanation.begin(), explanation.end(), (*subFormula)->pConstraint() ) != explanation.end() )
                    {
                        mInfeasibleSubsets.back().insert( *subFormula );
                    }
                }
                return false;
            }
        }
        return true;
    }

    /**
     * Checks the so far received constraints for consistency.
     *
     * @return  True,    if the conjunction of received constraints is consistent;
     *          False,   if the conjunction of received constraints is inconsistent;
     *          Unknown, otherwise.
     */
    Answer LRAModule::isConsistent()
    {
        if( mpLRASolver->checkA() )
        {
            if( mNumAddedNonlinearConstraints > 0 )
            {
                return runBackends();
            }
            else
            {
                return True;
            }
        }
        else
        {
            vector<const Constraint*> explanation = mpLRASolver->getExplanation();
            mInfeasibleSubsets.clear();
            mInfeasibleSubsets.push_back( set<const Formula*>() );
            for( Formula::const_iterator subFormula = receivedFormulaBegin(); subFormula != receivedFormulaEnd(); ++subFormula )
            {
                assert( (*subFormula)->getType() == REALCONSTRAINT );
                if( find( explanation.begin(), explanation.end(), (*subFormula)->pConstraint() ) != explanation.end() )
                {
                    mInfeasibleSubsets.back().insert( *subFormula );
                }
            }
            return False;
        }
    }

    /**
     * Pops the last backtrackpoint, from the stack of backtrackpoints.
     */
    void LRAModule::popBacktrackPoint()
    {
        for( unsigned i = mBackTrackPoints.back(); i < receivedFormulaSize(); ++i )
        {
            if( !receivedFormulaAt( i )->constraint().isLinear() )
            {
                --mNumAddedNonlinearConstraints;
            }
        }
        mpLRASolver->popBacktrackPointA();
        Module::popBacktrackPoint();
    }

    /**
     * Pushes a backtrackpoint, to the stack of backtrackpoints.
     */
    void LRAModule::pushBacktrackPoint()
    {
        Module::pushBacktrackPoint();
        mpLRASolver->pushBacktrackPointA();
    }

    /**
     * Adds the given constraint to the map of received constraints to the corresponding
     * constraints used in the lrasolver combined with polarities.
     *
     * @param _constraint   The constraint to add.
     *
     * @return An iterator to the element in the map mapping the giving constraint.
     */
    LRAModule::cons_to_cons_bool_pair_vec_map::const_iterator LRAModule::addConstraintToLRASolverConstraints( const Constraint* const _constraint )
    {
        cons_bool_pair_vec constraintPolarityPairs = cons_bool_pair_vec();

        cons_to_cons_bool_pair_vec_map::const_iterator citer = mLRASolverConstraints.find( _constraint );
        if( citer != mLRASolverConstraints.end() )
        {
            return citer;
        }
        else
        {
            if( _constraint->isLinear() )
            {
                //create constraint adequate for the lrasolver
                switch( _constraint->relation() )
                {
                    case CR_EQ:
                    {
                        Constraint* constraintA = new Constraint( _constraint->lhs(), CR_LEQ, _constraint->variables() );
                        Constraint* constraintB = new Constraint( _constraint->lhs(), CR_GEQ, _constraint->variables() );
                        constraintPolarityPairs.push_back( cons_bool_pair( constraintA, true ) );
                        constraintPolarityPairs.push_back( cons_bool_pair( constraintB, true ) );
                        break;
                    }
                    case CR_LEQ:
                    {
                        Constraint* constraint = new Constraint( *_constraint );
                        constraintPolarityPairs.push_back( cons_bool_pair( constraint, true ) );
                        break;
                    }
                    case CR_GEQ:
                    {
                        Constraint* constraint = new Constraint( *_constraint );
                        constraintPolarityPairs.push_back( cons_bool_pair( constraint, true ) );
                        break;
                    }
                    case CR_LESS:
                    {
                        Constraint* constraint = new Constraint( _constraint->lhs(), CR_GEQ, _constraint->variables() );
                        constraintPolarityPairs.push_back( cons_bool_pair( constraint, false ) );
                        break;
                    }
                    case CR_GREATER:
                    {
                        Constraint* constraint = new Constraint( _constraint->lhs(), CR_LEQ, _constraint->variables() );
                        constraintPolarityPairs.push_back( cons_bool_pair( constraint, false ) );
                        break;
                    }
                    default:
                    {
                        //                      cout << "Unexpected relation symbol. ( " << __func__ << ":" << __LINE__ << ")" << endl;
                        //                      assert( false );
                        //                      return mLRASolverConstraints.end();
                    }
                }
            }
            return mLRASolverConstraints.insert( pair<const Constraint* const , cons_bool_pair_vec>( _constraint, constraintPolarityPairs ) ).first;
        }
    }
}    // namespace smtrat

