
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
 * File:   FourierMotzkinSimplifier.cpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * Created on January 18, 2012, 3:51 PM
 */

#include "FourierMotzkinSimplifier.h"
#include "../NRATSolver.h"

//#define SIMPLE_DEBUG_BACKENDSS

using namespace std;
using namespace GiNaC;

namespace smtrat
{
    /**
     * Constructor
     */
    FourierMotzkinSimplifier::FourierMotzkinSimplifier( Manager* const _tsManager, const Formula* const _formula ):
        Module( _tsManager, _formula ),
        mFreshConstraintReceived( false ),
        mInconsistentConstraintAdded( false ),
        mAllVariables( symtab() )
    {
        this->mModuleType = MT_FourierMotzkinSimplifier;
    }

    /**
     * Destructor:
     */
    FourierMotzkinSimplifier::~FourierMotzkinSimplifier(){}

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
    bool FourierMotzkinSimplifier::assertSubformula( Formula::const_iterator _subformula )
    {
        assert( (*_subformula)->getType() == REALCONSTRAINT );
        Module::assertSubformula( _subformula );

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

    /**
     * Checks the so far received constraints for consistency.
     *
     * @return  TS_True,    if the conjunction of received constraints is consistent;
     *          TS_False,   if the conjunction of received constraints is inconsistent;
     *          TS_Unknown, otherwise.
     */
    Answer FourierMotzkinSimplifier::isConsistent()
    {
        if( !mFreshConstraintReceived )
        {
            if( mInfeasibleSubsets.empty() )
            {
                return True;
            }
            else
            {
                return False;
            }
        }
        mFreshConstraintReceived = false;
        if( mpReceivedFormula->empty() )
        {
            return True;
        }
        if( mInconsistentConstraintAdded )
        {
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
                    const Constraint* combinedConstraint = combine( *constraintA, *constraintB );
                    if( combinedConstraint != NULL )
                    {
                        cout << "combine( " << *constraintA << " , " << *constraintB << " )  =  " << *combinedConstraint << endl;
                        switch( combinedConstraint->isConsistent() )
                        {
                            case 0:
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
                            case 1:
                            {
                                /*
                                 * Remove condA from the set of redundant constraints, if it is insight.
                                 */
                                redundantFormulaSet.insert( *subformulaA );
                                redundantFormulaSet.insert( *subformulaB );
                                break;
                            }
                            case 2:
                            {
                                vec_set_const_pFormula originsA = vec_set_const_pFormula();
                                getOrigins( *subformulaA, originsA );
                                vec_set_const_pFormula originsB = vec_set_const_pFormula();
                                getOrigins( *subformulaB, originsB );

                                vec_set_const_pFormula originsAB = merge( originsA, originsB );
                                addSubformulaToPassedFormula( new Formula( combinedConstraint ), originsAB );

                                /*
                                 * Remove condA from the set of redundant constraints, if it is insight.
                                 */
                                redundantFormulaSet.insert( *subformulaA );
                                redundantFormulaSet.insert( *subformulaB );
                                break;
                            }
                            default:
                            {
                                cerr << "Unknown output!" << endl;
                                assert( false );
                            }
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
                return a;
            }
            else
            {
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
                    return False;
                }
                case 1:
                {
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
                    return a;
                }
                default:
                {
                    assert( false );
                    return Unknown;
                }
            }
        }
    }

    /**
     * Removes a everything related to a sub formula of the received formula.
     *
     * @param _subformula The sub formula of the received formula to remove.
     */
    void FourierMotzkinSimplifier::removeSubformula( Formula::const_iterator _subformula )
    {
        Module::removeSubformula( _subformula );
    }

    /**
     *
     * @param _constraintA
     * @param _constraintB
     * @return
     */
    const Constraint* FourierMotzkinSimplifier::combine( const Constraint& _constraintA, const Constraint& _constraintB )
    {
        ex lhsA = _constraintA.lhs().expand();
        ex lhsB = _constraintB.lhs().expand();
        if( _constraintA.relation() == CR_EQ || _constraintA.relation() ==CR_NEQ
            || _constraintB.relation() == CR_EQ || _constraintB.relation() ==CR_NEQ )
        {
            return NULL;
        }
        Constraint_Relation relation = CR_LEQ;
        switch( _constraintA.relation() )
        {
            case CR_LESS:
            {
                if( _constraintB.relation() == CR_LESS || _constraintB.relation() == CR_LEQ )
                {
                    lhsB = -lhsB;
                    lhsB = lhsB.expand();
                }
                relation = CR_LESS;
                break;
            }
            case CR_LEQ:
            {
                if( _constraintB.relation() == CR_LESS || _constraintB.relation() == CR_LEQ )
                {
                    lhsB = -lhsB;
                    lhsB = lhsB.expand();
                }
                if( _constraintB.relation() == CR_LESS || _constraintB.relation() == CR_GREATER )
                {
                    relation = CR_LESS;
                }
                break;
            }
            case CR_GREATER:
            {
                if( _constraintB.relation() == CR_GREATER || _constraintB.relation() == CR_GEQ )
                {
                    lhsB = -lhsB;
                    lhsB = lhsB.expand();
                }
                relation = CR_GREATER;
                break;
            }
            case CR_GEQ:
            {
                if( _constraintB.relation() == CR_GREATER || _constraintB.relation() == CR_GEQ )
                {
                    lhsB = -lhsB;
                    lhsB = lhsB.expand();
                }
                if( _constraintB.relation() == CR_LESS || _constraintB.relation() == CR_GREATER )
                {
                    relation = CR_GREATER;
                }
                else
                {
                    relation = CR_GEQ;
                }
                break;
            }
            default:
            {
                return NULL;
            }
        }
        ExNumNumPair cs = commonSummand( lhsA, lhsB );
        if( cs.first != 0 )
        {
            cout << "   lhsA = " << lhsA << endl;
            cout << "   lhsB = " << lhsB << endl;
            cout << "   relation = " << relation << endl;
            cout << "   cs.first = " << cs.first << endl;
            cout << "   cs.second.first = " << cs.second.first << endl;
            cout << "   cs.second.second = " << cs.second.second << endl;
            ex newlhs = abs( cs.second.second ) * lhsA - abs( cs.second.first ) * lhsB;
            cout << "   newlhs = " << newlhs << endl;
            return Formula::newConstraint( newlhs, relation );
        }
        return NULL;
    }

    /**
     *
     * @param _expressionA
     * @param _expressionB
     * @return
     */
    ExNumNumPair FourierMotzkinSimplifier::commonSummand( const ex& _expressionA, const ex& _expressionB )
    {
        if( is_exactly_a<add>( _expressionA ) )
        {
            if( is_exactly_a<mul>( _expressionB ) || is_exactly_a<symbol>( _expressionB ) )
            {
                ExNumPair numAndSymPartB = getNumericAndSymbolPart( _expressionB );
                for( GiNaC::const_iterator summand = _expressionA.begin(); summand != _expressionA.end(); ++summand )
                {
                    ExNumPair numAndSymPartA = getNumericAndSymbolPart( *summand );
                    if( numAndSymPartA.first == numAndSymPartB.first && numAndSymPartA.second*numAndSymPartB.second > 0 )
                    {
                        return ExNumNumPair( numAndSymPartA.first, NumPair( numAndSymPartA.second, numAndSymPartB.second ) );
                    }
                }
            }
            else if( is_exactly_a<add>( _expressionB ) )
            {
                GiNaC::const_iterator summandA = _expressionA.begin();
                GiNaC::const_iterator summandB = _expressionB.begin();
                while( summandA != _expressionA.end() && summandB != _expressionB.end() )
                {
                    if( ( is_exactly_a<mul>( *summandA ) || is_exactly_a<symbol>( *summandA ) )
                        && ( is_exactly_a<mul>( *summandB ) || is_exactly_a<symbol>( *summandB ) ) )
                    {
                        ExNumPair numAndSymPartA = getNumericAndSymbolPart( *summandA );
                        ExNumPair numAndSymPartB = getNumericAndSymbolPart( *summandB );
                        if( numAndSymPartA.first == numAndSymPartB.first && numAndSymPartA.second*numAndSymPartB.second > 0 )
                        {
                            return ExNumNumPair( numAndSymPartA.first, NumPair( numAndSymPartA.second, numAndSymPartB.second ) );
                        }
                    }
                    if( ex_is_less()( *summandA, *summandB ) )
                    {
                        ++summandA;
                    }
                    else
                    {
                        ++summandB;
                    }
                }
            }
        }
        else if( is_exactly_a<mul>( _expressionA ) || is_exactly_a<symbol>( _expressionA ) )
        {
            ExNumPair numAndSymPartA = getNumericAndSymbolPart( _expressionA );
            ExNumPair numAndSymPartB = getNumericAndSymbolPart( _expressionB );
            if( numAndSymPartA.first == numAndSymPartB.first && numAndSymPartA.second*numAndSymPartB.second > 0 )
            {
                return ExNumNumPair( numAndSymPartA.first, NumPair( numAndSymPartA.second, numAndSymPartB.second ) );
            }
        }
        return ExNumNumPair( 0, NumPair( 1, 1 ) );
    }

    /**
     *
     * @param _ex
     * @return
     */
    ExNumPair FourierMotzkinSimplifier::getNumericAndSymbolPart( const ex& _ex )
    {
        assert( is_exactly_a<mul>( _ex ) || is_exactly_a<symbol>( _ex ) );
        numeric numPart = 1;
        ex      symPart = 1;
        if( is_exactly_a<symbol>( _ex ) )
        {
            symPart = _ex;
        }
        else if( is_exactly_a<mul>( _ex ) )
        {
            for( GiNaC::const_iterator factor = _ex.begin(); factor != _ex.end(); ++factor )
            {
                assert( is_exactly_a<symbol>( *factor ) || is_exactly_a<numeric>( *factor ) );
                if( is_exactly_a<symbol>( *factor ) )
                {
                    symPart = symPart* (*factor);
                }
                else if( is_exactly_a<numeric>( *factor ) )
                {
                    numPart = numPart* ex_to<numeric>( *factor );
                }
            }
        }
        return ExNumPair( symPart, numPart );
    }

}    // namespace smtrat

