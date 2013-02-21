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
 * File:   SmartSimplifier.cpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * Created on January 18, 2012, 3:51 PM
 */

#include "SmartSimplifier.h"
#include "../NRATSolver.h"

//#define SIMPLE_DEBUG_BACKENDSS

using namespace std;
using namespace GiNaC;

namespace smtrat
{
    /**
     * Constructor
     */
    SmartSimplifier::SmartSimplifier( ModuleType _type, const Formula* const _formula, RuntimeSettings* _settings, bool& _conditional, Manager* const _manager ):
        Module( _type, _formula, _conditional, _manager ),
        mFreshConstraintReceived( false ),
        mInconsistentConstraintAdded( false ),
        mAllVariables( symtab() )
    {
        this->mModuleType = MT_SmartSimplifier;
    }

    /**
     * Destructor:
     */
    SmartSimplifier::~SmartSimplifier(){}

    /**
     * Methods:
     */

    /**
     * Adds a constraint to this module.
     *
     * @param _constraint The constraint to add to the already added constraints.
     *
     * @return  true,   if the constraint and all previously added constraints are consistent;
     *          false,  if the added constraint or one of the previously added ones is inconsistent.
     */
    bool SmartSimplifier::assertSubformula( Formula::const_iterator _subformula )
    {
        Module::assertSubformula( _subformula );
        if( (*_subformula)->getType() == REALCONSTRAINT )
        {
            /*
            * Check the consistency of the constraint to add.
            */
            switch( (*_subformula)->constraint().isConsistent() )
            {
                case 0:
                {
                    mInfeasibleSubsets.clear();
                    mInfeasibleSubsets.push_back( set<const Formula*>() );
                    mInfeasibleSubsets.back().insert( mpReceivedFormula->back() );
                    mInconsistentConstraintAdded = true;
                    mSolverState = False;
                    return false;
                }
                case 1:
                {
                    return true;
                }
                case 2:
                {
                    /*
                    * Add the variables of the new constraint to the history of all occured variables.
                    */
                    symtab::const_iterator var = (*_subformula)->constraint().variables().begin();
                    while( var != (*_subformula)->constraint().variables().end() )
                    {
                        mAllVariables.insert( pair<const string, symbol>( var->first, ex_to<symbol>( var->second ) ) );
                        var++;
                    }
                    mFreshConstraintReceived = true;
                    return true;
                }
                default:
                {
                    assert( false );
                    return true;
                }
            }
        }
        return true;
    }

    /**
     * Checks the so far received constraints for consistency.
     *
     * @return  TS_True,    if the conjunction of received constraints is consistent;
     *          TS_False,   if the conjunction of received constraints is inconsistent;
     *          TS_Unknown, otherwise.
     */
    Answer SmartSimplifier::isConsistent()
    {
        if( mpReceivedFormula->isConstraintConjunction() )
        {
            if( !mFreshConstraintReceived )
            {
                if( mInfeasibleSubsets.empty() )
                {
                    mSolverState = True;
                    return True;
                }
                else
                {
                    mSolverState = False;
                    return False;
                }
            }
            mFreshConstraintReceived = false;
            if( mpReceivedFormula->empty() )
            {
                mSolverState = True;
                return True;
            }
            if( mInconsistentConstraintAdded )
            {
                mSolverState = False;
                return False;
            }
            else if( mpReceivedFormula->size() > 1 )
            {
                set<const Formula*> redundantFormulaSet     = set<const Formula*>();
                Formula::iterator firstFreshPassedSubformula;
                bool firstFreshPassedSubformulaFound = false;
                Formula::const_iterator receivedSubformula = firstUncheckedReceivedSubformula();
                while( receivedSubformula != mpReceivedFormula->end() )
                {
                    addReceivedSubformulaToPassedFormula( receivedSubformula++ );
                    if( !firstFreshPassedSubformulaFound )
                    {
                        firstFreshPassedSubformula = mpPassedFormula->last();
                    }
                }

                /*
                * Check all constraint combinations.
                */
                bool comparisonBetweenFreshConstraints = false;
                Formula::iterator subformulaA = mpPassedFormula->begin();
                while( subformulaA != mpPassedFormula->end() )
                {
                    if( subformulaA == firstFreshPassedSubformula )
                    {
                        comparisonBetweenFreshConstraints = true;
                    }
                    Formula::iterator subformulaB;
                    if( comparisonBetweenFreshConstraints )
                    {
                        subformulaB = subformulaA;
                        ++subformulaB;
                    }
                    else
                    {
                        subformulaB = firstFreshPassedSubformula;
                    }
                    while( subformulaB != mpPassedFormula->end() )
                    {
                        const Constraint* constraintA = (*subformulaA)->pConstraint();
                        const Constraint* constraintB = (*subformulaB)->pConstraint();
                        switch( Constraint::compare( *constraintA, *constraintB ) )
                        {
                            case 2:
                            {
                                /*
                                * If the two constraints have the same solution space.
                                */
                                vec_set_const_pFormula originsA = vec_set_const_pFormula();
                                getOrigins( *subformulaA, originsA );
                                vec_set_const_pFormula originsB = vec_set_const_pFormula();
                                getOrigins( *subformulaB, originsB );

                                unsigned                         originsASizeBefore = originsA.size();
                                vec_set_const_pFormula::iterator originSetB         = originsB.begin();
                                while( originSetB != originsB.end() )
                                {
                                    unsigned i = 0;
                                    while( i < originsASizeBefore )
                                    {
                                        set<const Formula*>::const_iterator originA = originsA.at( i ).begin();
                                        set<const Formula*>::const_iterator originB = originSetB->begin();
                                        while( originA != originsA.at( i ).end() && originB != originSetB->end() )
                                        {
                                            if( originA != originB )
                                            {
                                                break;
                                            }
                                            ++originA;
                                            ++originB;
                                        }
                                        if( originA == originsA.at( i ).end() && originB == originSetB->end() )
                                        {
                                            break;
                                        }
                                        ++i;
                                    }
                                    if( i < originsASizeBefore )
                                    {
                                        originsA.push_back( *originSetB );
                                    }
                                    ++originSetB;
                                }
                                if( originsA.size() == originsASizeBefore )
                                {
                                    break;
                                }

                                addSubformulaToPassedFormula( new Formula( constraintA ), originsA );

                                redundantFormulaSet.insert( *subformulaA );
                                redundantFormulaSet.insert( *subformulaB );
                                break;
                            }
                            case 1:
                            {
                                /*
                                * If consA's solution space is a subset of the solution space of consB.
                                */
                                vec_set_const_pFormula originsA = vec_set_const_pFormula();
                                getOrigins( *subformulaA, originsA );
                                vec_set_const_pFormula originsB = vec_set_const_pFormula();
                                getOrigins( *subformulaB, originsB );

                                vec_set_const_pFormula originsAB = merge( originsA, originsB );

                                setOrigins( *subformulaA, originsAB );
                                redundantFormulaSet.insert( *subformulaB );
                                break;
                            }
                            case 0:
                            {
                                /*
                                * Cannot compare these constraints. Do nothing.
                                */
                                break;
                            }
                            case -1:
                            {
                                /*
                                * If condA's solution space is a superset of the solution space of consB.
                                */
                                vec_set_const_pFormula originsA = vec_set_const_pFormula();
                                getOrigins( *subformulaA, originsA );
                                vec_set_const_pFormula originsB = vec_set_const_pFormula();
                                getOrigins( *subformulaB, originsB );

                                vec_set_const_pFormula originsAB = merge( originsA, originsB );

                                setOrigins( *subformulaB, originsAB );
                                redundantFormulaSet.insert( *subformulaA );
                                break;
                            }
                            case -2:
                            {
                                redundantFormulaSet.erase( *subformulaA );
                                redundantFormulaSet.erase( *subformulaB );

                                /*
                                * If it is easy to decide that consA and consB are conflicting.
                                */

                                vec_set_const_pFormula originsA = vec_set_const_pFormula();
                                getOrigins( *subformulaA, originsA );
                                vec_set_const_pFormula originsB = vec_set_const_pFormula();
                                getOrigins( *subformulaB, originsB );

                                vec_set_const_pFormula originsAB = merge( originsA, originsB );
                                for( vec_set_const_pFormula::iterator setIter = originsAB.begin(); setIter != originsAB.end(); ++setIter )
                                {
                                    mInfeasibleSubsets.push_back( set<const Formula*>() );
                                    mInfeasibleSubsets.back().insert( setIter->begin(), setIter->end() );
                                }
                                break;
                            }
                            case -4:
                            {
                                redundantFormulaSet.erase( *subformulaA );
                                redundantFormulaSet.erase( *subformulaB );

                                /*
                                * If it is easy to decide that consA and consB are conflicting.
                                */

                                vec_set_const_pFormula originsA = vec_set_const_pFormula();
                                getOrigins( *subformulaA, originsA );
                                vec_set_const_pFormula originsB = vec_set_const_pFormula();
                                getOrigins( *subformulaB, originsB );

                                vec_set_const_pFormula originsAB = merge( originsA, originsB );
                                for( vec_set_const_pFormula::iterator setIter = originsAB.begin(); setIter != originsAB.end(); ++setIter )
                                {
                                    mInfeasibleSubsets.push_back( set<const Formula*>() );
                                    mInfeasibleSubsets.back().insert( setIter->begin(), setIter->end() );
                                }
                                break;
                            }
                            case -3:
                            {
                                /*
                                * If it is easy to give a condition whose solution space is the intersection of
                                * the solution spaces of consA and consB.
                                */
                                Constraint_Relation rel = CR_EQ;
                                if( (constraintA->relation() == CR_GEQ && constraintB->relation() == CR_GEQ)
                                        || (constraintA->relation() == CR_GEQ && constraintB->relation() == CR_LEQ)
                                        || (constraintA->relation() == CR_LEQ && constraintB->relation() == CR_GEQ)
                                        || (constraintA->relation() == CR_LEQ && constraintB->relation() == CR_LEQ) )
                                {
                                }
                                else if( (constraintA->relation() == CR_NEQ && constraintB->relation() == CR_GEQ)
                                        || (constraintA->relation() == CR_GEQ && constraintB->relation() == CR_NEQ) )
                                {
                                    rel = CR_GREATER;
                                }
                                else if( (constraintA->relation() == CR_NEQ && constraintB->relation() == CR_LEQ)
                                        || (constraintA->relation() == CR_LEQ && constraintB->relation() == CR_NEQ) )
                                {
                                    rel = CR_LESS;
                                }
                                else
                                {
                                    assert( false );
                                }

                                vec_set_const_pFormula originsA = vec_set_const_pFormula();
                                getOrigins( *subformulaA, originsA );
                                vec_set_const_pFormula originsB = vec_set_const_pFormula();
                                getOrigins( *subformulaB, originsB );

                                vec_set_const_pFormula originsAB = merge( originsA, originsB );
                                addSubformulaToPassedFormula( new Formula( Formula::newConstraint( constraintB->lhs(), rel, constraintB->variables() ) ), originsAB );

                                /*
                                * Remove condA from the set of redundant constraints, if it is insight.
                                */
                                redundantFormulaSet.insert( *subformulaA );
                                redundantFormulaSet.insert( *subformulaB );
                                break;
                            }
                            default:
                            {
                                assert( false );
                            }
                        }
                        ++subformulaB;
                    }
                    ++subformulaA;
                }

                /*
                * Delete the redundant constraints of the vector of constraints to simplify.
                */
                Formula::iterator passedSubformula = mpPassedFormula->begin();
                while( passedSubformula != mpPassedFormula->end() )
                {
                    if( redundantFormulaSet.find( *passedSubformula ) != redundantFormulaSet.end() )
                    {
                        passedSubformula = removeSubformulaFromPassedFormula( passedSubformula );
                    }
                    else
                    {
                        ++passedSubformula;
                    }
                }
                if( mInfeasibleSubsets.empty() )
                {
                    Answer a = runBackends();
                    if( a == False )
                    {
                        getInfeasibleSubsets();
                    }
                    mSolverState = a;
                    return a;
                }
                else
                {
                    mSolverState = False;
                    return False;
                }
            }
            else
            {
                /*
                * Only one constraint received.
                */
                switch( mpReceivedFormula->back()->constraint().isConsistent() )
                {
                    case 0:
                    {
                        mSolverState = False;
                        return False;
                    }
                    case 1:
                    {
                        mSolverState = True;
                        return True;
                    }
                    case 2:
                    {
                        addReceivedSubformulaToPassedFormula( firstUncheckedReceivedSubformula() );
                        Answer a = runBackends();
                        if( a == False )
                        {
                            getInfeasibleSubsets();
                        }
                        mSolverState = a;
                        return a;
                    }
                    default:
                    {
                        assert( false );
                        mSolverState = Unknown;
                        return Unknown;
                    }
                }
            }
        }
        else
        {
            return Unknown;
        }
    }

    /**
     * Removes a everything related to a sub formula of the received formula.
     *
     * @param _subformula The sub formula of the received formula to remove.
     */
    void SmartSimplifier::removeSubformula( Formula::const_iterator _subformula )
    {
        Module::removeSubformula( _subformula );
    }

}    // namespace smtrat

