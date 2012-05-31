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
 * File:   VSModule.cpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * Created on January 18, 2012, 3:45 PM
 */

#include "VSModule.h"

using namespace std;
using namespace GiNaC;
using namespace vs;

namespace smtrat
{
    /**
     * Constructors:
     */

    VSModule::VSModule( Manager* const _tsManager, const Formula* const _formula ):
        Module( _tsManager, _formula )
    {
        mModuleType                   = MT_VSModule;
#ifdef VS_DEBUG
        debug                         = true;
#else
        debug                         = false;
#endif
#ifdef VS_DEBUG_METHODS
        debugmethods                  = true;
#else
        debugmethods                  = false;
#endif
        mInconsistentConstraintAdded  = false;
        mFreshConstraintReceived      = false;
        mIDCounter                    = 0;
        mpStateTree                   = new State();
        mpRanking                     = new ValuationMap();
        mReceivedConstraintsAsConditions  = ConstraintConditionMap();
    }

    /**
     * Destructor:
     */
    VSModule::~VSModule()
    {
        while( !mReceivedConstraintsAsConditions.empty() )
        {
            vs::Condition* pRecCond = mReceivedConstraintsAsConditions.begin()->second;
            mReceivedConstraintsAsConditions.erase( mReceivedConstraintsAsConditions.begin() );
            delete pRecCond;
        }
        delete mpRanking;
        delete mpStateTree;
    }

    /**
     * @param _constraint The constraint to add to the already added constraints.
     */
    bool VSModule::assertSubFormula( const Formula* const _formula )
    {
    	assert( _formula->getType() == REALCONSTRAINT );
		Module::assertSubFormula( _formula );
        if( debugmethods )
        {
            cout << __func__ << endl;
        }

        vs::Condition* condition = new vs::Condition( _formula->constraint() );
        mReceivedConstraintsAsConditions[_formula->pConstraint()] = condition;
        /*
         * Clear the ranking.
         */
        switch( _formula->constraint().isConsistent() )
        {
        case 0:
        {
            eraseDTsOfRanking( *mpStateTree );
            mIDCounter = 0;
            mInfeasibleSubsets.clear();
            mInfeasibleSubsets.push_back( set< const Formula* >() );
            mInfeasibleSubsets.back().insert( receivedFormulaBack() );
            mInconsistentConstraintAdded = true;
            return false;
        }
        case 1:
        {
            return true;
        }
        case 2:
        {
            eraseDTsOfRanking( *mpStateTree );
            mIDCounter = 0;
            symtab::const_iterator var = _formula->constraint().variables().begin();
            while( var != _formula->constraint().variables().end() )
            {
                mAllVariables.insert( pair<const string, symbol>( var->first, ex_to<symbol>( var->second ) ) );
                var++;
            }
            ConditionSet oConds = ConditionSet();
            oConds.insert( condition );

            vector<DisjunctionOfConditionConjunctions> subResults = vector<DisjunctionOfConditionConjunctions>();
            DisjunctionOfConditionConjunctions subResult = DisjunctionOfConditionConjunctions();
            ConditionVector condVector                   = ConditionVector();
            condVector.push_back( new vs::Condition( _formula->constraint(), false, oConds, 0 ));
            subResult.push_back( condVector );
            subResults.push_back( subResult );
            mpStateTree->addSubstitutionResults( subResults );

            insertDTinRanking( mpStateTree );
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
     * @return  True,    if the conjunction of all already added constraints consistent;
     *          False,   if the conjunction of all already added constraints inconsistent;
     *          Unknown, otherwise.
     */
    Answer VSModule::isConsistent()
    {
        if( debugmethods )
        {
            cout << __func__ << endl;
        }
        if( !mFreshConstraintReceived )
        {
            if( mInfeasibleSubsets.empty() )
            {
                //printAnswer( cout );
                return True;
            }
            else
            {
                return False;
            }
        }
        mFreshConstraintReceived = false;
        if( receivedFormulaEmpty() )
        {
            return True;
        }
        if( mInconsistentConstraintAdded )
        {
            return False;
        }
#ifndef VS_INCREMENTAL
        reset();
#endif

        while( !mpRanking->empty() )
        {
            State* currentState = mpRanking->begin()->second;

            if( currentState->hasChildrenToInsert() )
            {
                currentState->rHasChildrenToInsert() = false;
                insertDTsinRanking( currentState );
            }
            else
            {
                currentState->simplify();
                if( debug )
                {
                    cout << "*** Considered state:" << endl;
                    currentState->printAlone( "   ", cout );
                }
                if( currentState->isInconsistent() )
                {
                    eraseDTsOfRanking( *currentState );
                    if( currentState->isRoot() )
                    {
                        updateInfeasibleSubset();
                    }
                    else
                    {
                        if( currentState->passConflictToFather() )
                        {
                            insertDTinRanking( currentState );
                        }
                        else
                        {
                            eraseDTsOfRanking( currentState->rFather() );
                            insertDTinRanking( currentState->pFather() );
                        }
                    }
                }
                else if( currentState->hasRecentlyAddedConditions() )
                {
                    if( debug )
                    {
                        cout << "*** Propagate new conditions :" << endl;
                    }
                    propagateNewConditions(currentState);
                    if( debug )
                    {
                        cout << "*** Propagate new conditions ready." << endl;
                    }
                }
                else
                {
                    switch( currentState->stateType() )
                    {
                    case SUBSTITUTION_TO_APPLY:
                    {
                        if( debug )
                        {
                            cout << "*** SubstituteAll changes it to:" << endl;
                        }
                        if( !substituteAll( currentState, currentState->rFather().rConditions() ))
                        {
                            /*
                             * Delete the currently considered state.
                             */
                            currentState->rInconsistent() = true;
                            eraseDTofRanking( *currentState );
                        }
                        if( debug )
                        {
                            cout << "*** SubstituteAll ready." << endl;
                        }
                        break;
                    }
                    case COMBINE_SUBRESULTS:
                    {
                        if( debug )
                        {
                            cout << "*** Refresh conditons:" << endl;
                        }
                        if( currentState->nextSubResultCombination() )
                        {
                            if( currentState->refreshConditions() )
                            {
                                insertDTinRanking( currentState );
                            }
                            else
                            {
                                insertDTsinRanking( currentState );
                            }
                            if( debug )
                            {
                                currentState->printAlone( "   ", cout );
                            }
                        }
                        else
                        {
                            /*
                             * If it was the last combination, delete the state.
                             */
                            currentState->rInconsistent() = true;
                            eraseDTsOfRanking( *currentState );
                        }
                        if( debug )
                        {
                            cout << "*** Conditions refreshed." << endl;
                        }
                        break;
                    }
                    case TEST_CANDIDATE_TO_GENERATE:
                    {
                        /*
                         * Set the index, if not already done, to the best variable to eliminate next.
                         */
                        if( currentState->index() == "" )
                        {
                            currentState->initIndex( mAllVariables );
                        }
                        else if( currentState->tryToRefreshIndex() )
                        {
                            if( currentState->initIndex( mAllVariables ))
                            {
                                currentState->initConditionFlags();
                                while( !currentState->children().empty() )
                                {
                                    eraseDTsOfRanking( *currentState->rChildren().back() );
                                    delete currentState->rChildren().back();
                                }
                            }
                        }

                        /*
                         * Find the most adequate conditions to continue.
                         */
                        vs::Condition * currentCondition;
                        if( !currentState->bestCondition( currentCondition, mAllVariables.size() ))
                        {
                            /*
                             * It is a state, where no more elimination could be applied to the conditions.
                             */
                            if( currentState->conditions().empty() )
                            {
                                /*
                                 * Check if there are still conditions in any ancestor, which have not been considered.
                                 */
                                State * unfinishedAncestor;
                                if( currentState->unfinishedAncestor( unfinishedAncestor ))
                                {
                                    /*
                                     * Go back to this ancestor and refine.
                                     */
                                    eraseDTsOfRanking( *unfinishedAncestor );
                                    unfinishedAncestor->extendSubResultCombination();
                                    unfinishedAncestor->rStateType() = COMBINE_SUBRESULTS;
                                    if( unfinishedAncestor->refreshConditions() )
                                    {
                                        insertDTinRanking( unfinishedAncestor );
                                    }
                                    else
                                    {
                                        insertDTsinRanking( unfinishedAncestor );
                                    }
                                }
                                else
                                {
                                    /*
                                     * Solution.
                                     */
                                    if( debug )
                                    {
                                        printAll( cout );
                                    }
                                    //printAnswer( cout );
                                    return True;
                                }
                            }

                            /*
                             * It is a state, where all conditions have been used for test candidate generation.
                             */
                            else
                            {
                                /*
                                 * Check whether there are still test candidates in form of children left.
                                 */
                                bool                  currentStateHasChildrenToConsider       = false;
                                bool                  currentStateHasChildrenWithToHighDegree = false;
                                StateVector::iterator child                                   = currentState->rChildren().begin();
                                while( child != currentState->children().end() )
                                {
                                    if( !(**child).isInconsistent() )
                                    {
                                        if( !(**child).markedAsDeleted() )
                                        {
                                            insertDTinRanking( *child );
                                        }
                                        if( !(**child).toHighDegree() &&!(**child).markedAsDeleted() )
                                        {
                                            currentStateHasChildrenToConsider = true;
                                        }
                                        else
                                        {
                                            currentStateHasChildrenWithToHighDegree = true;
                                        }
                                    }
                                    child++;
                                }

                                if( !currentStateHasChildrenToConsider )
                                {
                                    if( !currentStateHasChildrenWithToHighDegree )
                                    {
                                        currentState->rInconsistent() = true;
                                        eraseDTsOfRanking( *currentState );
                                        if( currentState->isRoot() )
                                        {
                                            updateInfeasibleSubset();
                                        }
                                        else
                                        {
                                            if( currentState->passConflictToFather() )
                                            {
                                                insertDTinRanking( currentState );
                                            }
                                            else
                                            {
                                                eraseDTsOfRanking( currentState->rFather() );
                                                insertDTinRanking( currentState->pFather() );
                                            }
                                        }
                                    }
                                    else
                                    {
                                        currentState->rMarkedAsDeleted() = true;
                                        eraseDTofRanking( *currentState );
                                    }
                                }
                            }
                        }

                        /*
                         * Generate test candidates for the chosen variable and the chosen condition.
                         */
                        else
                        {
                            /*
                             * The degree of the constraint is appropriate to applicate this version of the
                             * virtual substitution.
                             */
                            symtab::const_iterator var = currentCondition->constraint().variables().find( currentState->index() );
                            if( var != currentCondition->constraint().variables().end() )
                            {
                                if( debug )
                                {
                                    cout << "*** Eliminate " << currentState->index() << " in ";
                                    currentCondition->rConstraint().print( cout );
                                    cout << " creates:" << endl;
                                }
                                if( eliminate( currentState, currentState->index(), currentCondition ))
                                {
                                    if( debug )
                                    {
                                        cout << "*** Eliminate ready." << endl;
                                    }
                                }
                                else
                                {
                                    if( debug )
                                    {
                                        cout << "*** No elimination. (Too high degree)" << endl;
                                    }
#ifdef VS_DELAY_BACKEND_CALL
                                    if( (*currentState).toHighDegree() )
                                    {
#endif

                                        /*
                                         * If we need to involve a complete approach.
                                         */
#ifdef VS_WITH_BACKEND
                                        switch( runBackendSolvers( currentState ))
                                        {
                                        case True:
                                        {
                                            currentState->rToHighDegree() = true;
                                            //printAnswer( cout );
                                            return True;
                                        }
                                        case False:
                                        {
                                            currentState->rToHighDegree() = true;
                                            break;
                                        }
                                        case Unknown:
                                        {
                                            if( !currentState->rToHighDegree() )
                                            {
                                                currentState->rToHighDegree() = true;
                                                insertDTinRanking( currentState );
                                                break;
                                            }
                                            else
                                            {
                                                return Unknown;
                                            }
                                        }
                                        default:
                                        {
                                            cout << "Error: Unknown answer in method " << __func__ << " line " << __LINE__ << endl;
                                            return Unknown;
                                        }
                                        }
#else
                                        currentState->printAlone( "   ", cout );
                                        cout << "###" << endl;
                                        cout << "###                  Unknown!" << endl;
                                        cout << "###" << endl;
                                        return Unknown;
#endif
#ifdef VS_DELAY_BACKEND_CALL
                                    }
                                    else
                                    {
                                        currentState->rToHighDegree() = true;
                                        insertDTinRanking( currentState );
                                    }
#endif
                                }
                            }
                            else
                            {
                                (*currentCondition).rFlag() = true;

                                /*
                                 * Update the ranking entry of the state.
                                 */
                                insertDTinRanking( currentState );
                            }
                        }
                        break;
                    }
                    default:
                        assert( false );
                    }
                }
            }
        }
        updateInfeasibleSubset();
        return False;
    }

    /**
     * Backtracks until the last backtrack point.
     */
    void VSModule::popBacktrackPoint()
    {
        if( debugmethods )
        {
            cout << __func__ << endl;
        }
        assert( !mBackTrackPoints.empty() );

#ifdef VS_BACKTRACKING
        eraseDTsOfRanking( *mpStateTree );
        ConditionVector condsToDelete  = ConditionVector();
        ConditionVector condsToDeleteB = ConditionVector();
        assert( mpStateTree->hasSubstitutionResults() );
        assert( mpStateTree->substitutionResults().size() == 1 );
        assert( mpStateTree->substitutionResults().back().size() == 1 );
        assert( receivedFormulaSize() == mpStateTree->substitutionResults().back().back().first.size() );
#endif
		Module::popBacktrackPoint();
		signed uRFS = receivedFormulaSize();
        for( signed pos = lastBacktrackpointsEnd()+1; pos < uRFS; ++pos )
        {
            vs::Condition* pCondition = mReceivedConstraintsAsConditions[receivedFormulaAt( pos )->pConstraint()];
            mReceivedConstraintsAsConditions.erase( receivedFormulaAt( pos )->pConstraint() );
            delete pCondition;
        }
#ifdef VS_BACKTRACKING
		bool firstConstraintToRemoveFound = false;
		for( ConditionVector::iterator cond = mpStateTree->rSubstitutionResults().back().back().first.begin();
			 cond != mpStateTree->rSubstitutionResults().back().back().first.end();
			 ++cond )
		{
			if( firstConstraintToRemoveFound )
			{
				condsToDeleteB.push_back( *cond );
				mpStateTree->rSubstitutionResults().back().back().first.erase( cond );
			}
			else if( (*cond)->constraint() == **constraintsToRemove.begin() )
			{
				condsToDeleteB.push_back( *cond );
				mpStateTree->rSubstitutionResults().back().back().first.erase( cond );
				firstConstraintToRemoveFound = true;
			}
		}
		assert( firstConstraintToRemoveFound );

        /*
         * Collect the conditions having the conditions to delete as original conditions.
         */
        ConditionVector conditionsToDeleteInRoot = ConditionVector();
        for( ConditionVector::iterator cond = mpStateTree->rConditions().begin(); cond != mpStateTree->conditions().end(); ++cond )
        {
            bool                   originalConditionDeleted = false;
            ConditionSet::iterator oCond                    = (**cond).rOriginalConditions().begin();
            while( oCond != (**cond).originalConditions().end() )
            {
                ConditionVector::const_iterator condToDel = condsToDelete.begin();
                while( condToDel != condsToDelete.end() )
                {
                    if( *oCond == *condToDel )
                    {
                        break;
                    }
                    condToDel++;
                }
                if( condToDel != condsToDelete.end() )
                {
                    (**cond).rOriginalConditions().erase( oCond++ );
                    originalConditionDeleted = true;
                }
                else
                {
                    oCond++;
                }
            }
            if( originalConditionDeleted )
            {
                conditionsToDeleteInRoot.push_back( *cond );
            }
        }

        /*
         * Delete the conditions having only conditions to delete as original conditions.
         */
        mpStateTree->deleteConditions( conditionsToDeleteInRoot );

        while( !condsToDelete.empty() )
        {
            vs::Condition* rpCond = condsToDelete.back();
            condsToDelete.pop_back();
            delete rpCond;
        }

        while( !condsToDeleteB.empty() )
        {
            vs::Condition* rpCond = condsToDeleteB.back();
            condsToDeleteB.pop_back();
            delete rpCond;
        }

        mpStateTree->rTakeSubResultCombAgain() = true;

        insertDTsinRanking( mpStateTree );
        mpStateTree->rTakeSubResultCombAgain() = true;
#endif

#ifndef VS_BACKTRACKING
#ifdef VS_INCREMENTAL
        reset();
#endif
#endif

        mFreshConstraintReceived = true;
    }

    /**
     * Eliminates the given variable by finding test candidates of the constraint of the given
     * condition. All this happens in the state _currentState.
     *
     * @param _currentState     The currently considered state.
     * @param _eliminationVar   The substitution to apply.
     * @param _condition        The condition with the constraint, in which should be substituted.
     *
     * @sideeffect: For each test candidate a new child of the currently considered state
     *              is generated. The solved constraint in the currently considered
     *              state now is labeled by true, which means, that the constraint
     *              already served to eliminate for the respective variable in this
     *              state.
     */
    bool VSModule::eliminate( State* _currentState, const string& _eliminationVar, vs::Condition* _condition )
    {
#ifdef VS_DEBUG_METHODS
        cout << __func__ << " " << _eliminationVar << " in ";
        (*_condition).constraint().print( cout );
        cout << endl;
#endif

        /*
         * Get the constraint of this condition.
         */
        const Constraint& constraint = (*_condition).constraint();

        /*
         * Get coefficients of the variable in the constraints.
         */
        symbol sym;
        constraint.variable( _eliminationVar, sym );

        /*
         * Determine the substitution type: normal or +epsilon
         */
        Substitution_Type subType = ST_PLUS_EPSILON;
        if( constraint.relation() == CR_EQ || constraint.relation() == CR_LEQ || constraint.relation() == CR_GEQ )
        {
            subType = ST_NORMAL;
        }

        ex lhs = constraint.lhs();
        if( lhs.degree( ex( sym ) ) > 1 )
        {
            ex derivate            = lhs.diff( sym, 1 );
            ex gcdOfLhsAndDerivate = gcd( lhs, derivate );
            gcdOfLhsAndDerivate    = gcdOfLhsAndDerivate.expand().normal();
            if( gcdOfLhsAndDerivate != 1 )
            {
                ex quotient;
                if( divide( lhs, gcdOfLhsAndDerivate, quotient ))
                {
                    lhs = quotient.expand().normal();
                }
            }
        }

        vector<ex> coeffs = vector<ex>();
        for( signed i = 0; i <= lhs.degree( ex( sym ) ); ++i )
        {
            coeffs.push_back( ex( lhs.expand().coeff( ex( sym ), i )));
        }

        ConditionSet oConditions = ConditionSet();
        oConditions.insert( _condition );

        bool     generatedTestCandidateBeingASolution = false;
        unsigned numberOfAddedChildren                = 0;

        /*
         * Generate test candidates for the chosen variable considering the chosen constraint.
         */
        switch( coeffs.size() )
        {
        case 1:
        {
        	assert( false );
        	return false;
        }
        //degree = 1
        case 2:
        {
            /*
             * Create state ({b!=0} + oldConditions,
             *                        [x -> -c/b]):
             */
            if( (*_currentState).addChild( coeffs.at( 1 ), CR_NEQ, constraint.variables(), _eliminationVar, -coeffs.at( 0 ), 0, coeffs.at( 1 ), 0,
                                           subType, oConditions ))
            {
                if( constraint.relation() == CR_EQ )
                {
                    if( coeffs.at( 1 ).info( info_flags::rational ))
                    {
                        _currentState->rChildren().back()->setOriginalCondition( _condition );
                        generatedTestCandidateBeingASolution = true;
                    }
                }

                /*
                 * Add its valuation to the current ranking.
                 */
                insertDTinRanking( (*_currentState).rChildren().back() );
                numberOfAddedChildren++;
                if( debug )
                {
                    (*(*_currentState).rChildren().back()).print( "   ", cout );
                }
            }
            break;
        }
        //degree = 2
        case 3:
        {
            ex radicand = ex( pow( coeffs.at( 1 ), 2 ) - 4 * coeffs.at( 2 ) * coeffs.at( 0 ));
#ifdef VS_USE_GINAC_EXPAND
            radicand    = radicand.expand();
#endif
#ifdef VS_USE_GINAC_NORMAL
            radicand    = radicand.normal();
#endif

            /*
             * Create state ({a==0, b!=0} + oldConditions,
             *                        [x -> -c/b]):
             */
            if( (*_currentState).addChild( coeffs.at( 2 ), CR_EQ, coeffs.at( 1 ), CR_NEQ, constraint.variables(), _eliminationVar, -coeffs.at( 0 ),
                                           0, coeffs.at( 1 ), 0, subType, oConditions ))
            {
                if( constraint.relation() == CR_EQ )
                {
                    if( coeffs.at( 2 ).info( info_flags::rational ) && coeffs.at( 1 ).info( info_flags::rational ))
                    {
                        _currentState->rChildren().back()->setOriginalCondition( _condition );
                        generatedTestCandidateBeingASolution = true;
                    }
                }

                /*
                 * Add its valuation to the current ranking.
                 */
                insertDTinRanking( (*_currentState).rChildren().back() );
                numberOfAddedChildren++;
                if( debug )
                {
                    (*(*_currentState).rChildren().back()).print( "   ", cout );
                }
            }

            /*
             * Create state ({a!=0, b^2-4ac>=0} + oldConditions,
             *                        [x -> (-b+sqrt(b^2-4ac))/2a]):
             */
            if( (*_currentState).addChild( coeffs.at( 2 ), CR_NEQ, radicand, CR_GEQ, constraint.variables(), _eliminationVar, -coeffs.at( 1 ), 1,
                                           2 * coeffs.at( 2 ), radicand, subType, oConditions ))
            {
                if( constraint.relation() == CR_EQ )
                {
                    if( coeffs.at( 2 ).info( info_flags::rational ) && radicand.info( info_flags::rational ))
                    {
                        _currentState->rChildren().back()->setOriginalCondition( _condition );
                        generatedTestCandidateBeingASolution = true;
                    }
                }

                /*
                 * Add its valuation to the current ranking.
                 */
                insertDTinRanking( (*_currentState).rChildren().back() );
                numberOfAddedChildren++;
                if( debug )
                {
                    (*(*_currentState).rChildren().back()).print( "   ", cout );
                }
            }

            /*
             * Create state ({a!=0, b^2-4ac>0} + oldConditions,
             *                        [x -> (-b-sqrt(b^2-4ac))/2a]):
             */
            if( (*_currentState).addChild( coeffs.at( 2 ), CR_NEQ, radicand, CR_GREATER, constraint.variables(), _eliminationVar, -coeffs.at( 1 ),
                                           -1, 2 * coeffs.at( 2 ), radicand, subType, oConditions ))
            {
                if( constraint.relation() == CR_EQ )
                {
                    if( coeffs.at( 2 ).info( info_flags::rational ) && radicand.info( info_flags::rational ))
                    {
                        _currentState->rChildren().back()->setOriginalCondition( _condition );
                        generatedTestCandidateBeingASolution = true;
                    }
                }

                /*
                 * Add its valuation to the current ranking.
                 */
                insertDTinRanking( (*_currentState).rChildren().back() );
                numberOfAddedChildren++;
                if( debug )
                {
                    (*(*_currentState).rChildren().back()).print( "   ", cout );
                }
            }
            break;
        }
#ifdef VS_CUBIC_CASE
        //degree = 3
        case 4:
        {
            break;
        }
#endif
        //degree > 2 (> 3)
        default:
        {
            return false;
        }
        }

        if( !generatedTestCandidateBeingASolution )
        {
            /*
             * Create state ( Conditions,
             *                [x -> -infinity]):
             */
            if( (*_currentState).addChild( _eliminationVar, ST_MINUS_INFINITY, oConditions ))
            {
                /*
                 * Add its valuation to the current ranking.
                 */
                insertDTinRanking( (*_currentState).rChildren().back() );
                numberOfAddedChildren++;
                if( debug )
                {
                    (*(*_currentState).rChildren().back()).print( "   ", cout );
                }
            }
        }

        if( generatedTestCandidateBeingASolution )
        {
            for( ConditionVector::iterator cond = _currentState->rConditions().begin(); cond != _currentState->conditions().end(); ++cond )
            {
                (**cond).rFlag() = true;
            }
            assert( numberOfAddedChildren <= _currentState->children().size() );

            while( _currentState->children().size() > numberOfAddedChildren )
            {
                delete *_currentState->rChildren().begin();
            }
        }
        else
        {
            (*_condition).rFlag() = true;
        }

        insertDTinRanking( _currentState );

        return true;
    }

    /**
     * Applies the most recent substitution of _currentState to all conditions in it.
     *
     * @param _currentState     The currently considered state.
     * @param _conditions       The conditions of the state to which the substitution in this
     *                          state shall be applied.
     *
     * @sideeffect: For each case a new brother of the currently considered decision
     *              tuple is generated. The currently considered state gets
     *              deleted.
     */
    bool VSModule::substituteAll( State* _currentState, ConditionVector& _conditions )
    {
        if( debugmethods )
        {
            cout << __func__ << endl;
        }

        /*
         * Create a vector to store the results of each single substitution. Each entry correponds to
         * the results of a single substitution. These results can be considered as a disjunction of
         * conjunctions of constraints.
         */
        vector<DisjunctionOfConditionConjunctions> disjunctionsOfCondConj;
        disjunctionsOfCondConj = vector<DisjunctionOfConditionConjunctions>();

        /*
         * The substitution to apply.
         */
        assert( !_currentState->isRoot() );
        const Substitution& currentSubstitution = _currentState->substitution();

        /*
         * The variable to substitute.
         */
        const string& substitutionVariable = currentSubstitution.variable();

        /*
         * The conditions of the currently considered state, without
         * the one getting just eliminated.
         */
        ConditionVector oldConditions = ConditionVector();

        bool anySubstitutionFailed = false;
        ConditionSetSet conflictSet = ConditionSetSet();

        /*
         * Apply the most recent substitution in this state to each of its conditions.
         */
        for( ConditionVector::iterator cond = _conditions.begin(); cond != _conditions.end(); ++cond )
        {
            /*
             * The constraint to substitute in.
             */
            Constraint& currentConstraint = (**cond).rConstraint();

            /*
             * Does the condition contain the variable to substitute.
             */
            symtab::iterator var = currentConstraint.rVariables().find( substitutionVariable );
            if( var == currentConstraint.variables().end() )
            {
                if( !anySubstitutionFailed )
                {
                    /*
                     * If the variable to substitute does not occur in the condition,
                     * add the condition to the vector of conditions we just add to the
                     * states we create.
                     */
                    oldConditions.push_back( new vs::Condition( (**cond).constraint(), (**cond).valuation() ));
                    oldConditions.back()->rOriginalConditions().insert( *cond );
                }
            }
            else
            {
                /*
                 * Apply the substitution to each condition, in which the variable to substitute
                 * occurs and collect the results.
                 */
                DisjunctionOfConstraintConjunctions disjunctionOfConsConj;
                disjunctionOfConsConj = DisjunctionOfConstraintConjunctions();
                substitute( currentConstraint, currentSubstitution, disjunctionOfConsConj );

                /*
                 * Create the the conditions according to the just created constraint prototypes.
                 */
                bool anyConjunctionConsistent = false;
                disjunctionsOfCondConj.push_back( DisjunctionOfConditionConjunctions() );
                DisjunctionOfConditionConjunctions& currentDisjunction = disjunctionsOfCondConj.back();
                for( DisjunctionOfConstraintConjunctions::iterator consConj = disjunctionOfConsConj.begin(); consConj != disjunctionOfConsConj.end();
                        ++consConj )
                {
                    bool conjunctionConsistent = true;

                    /*
                     * Check if the conjunction contains any inconsistent constraint.
                     */
                    for( TS_ConstraintConjunction::iterator cons = consConj->begin(); cons != consConj->end(); ++cons )
                    {
                        if( (**cons).isConsistent() == 0 )
                        {
                            conjunctionConsistent = false;
                            break;
                        }
                    }
                    if( conjunctionConsistent )
                    {
                        anyConjunctionConsistent = true;

                        if( !anySubstitutionFailed )
                        {
                            currentDisjunction.push_back( ConditionVector() );
                            ConditionVector& currentConjunction = currentDisjunction.back();
                            for( TS_ConstraintConjunction::iterator cons = consConj->begin(); cons != consConj->end(); ++cons )
                            {
                                /*
                                 * Add all conditions to the conjunction, which are not variable-free and consistent.
                                 */
                                if( (**cons).isConsistent() != 1 )
                                {
                                    currentConjunction.push_back( new vs::Condition( **cons, _currentState->treeDepth() ));
                                    currentConjunction.back()->rOriginalConditions().insert( *cond );
                                }
                            }
                        }
                        else
                            break;
                    }
                }
                if( !anyConjunctionConsistent )
                {
                    anySubstitutionFailed = true;
                    ConditionSet condSet  = ConditionSet();
                    condSet.insert( *cond );
                    if( _currentState->pOriginalCondition() != NULL )
                    {
                        condSet.insert( _currentState->pOriginalCondition() );
                    }
                    conflictSet.insert( condSet );
                }
                while( !disjunctionOfConsConj.empty() )
                {
                    while( !disjunctionOfConsConj.back().empty() )
                    {
                        Constraint*& rpCons = disjunctionOfConsConj.back().back();
                        disjunctionOfConsConj.back().pop_back();
                        delete rpCons;
                    }
                    disjunctionOfConsConj.pop_back();
                }
            }
        }
        if( anySubstitutionFailed )
        {
            _currentState->rFather().addConflicts( _currentState->pSubstitution(), conflictSet );
            _currentState->rInconsistent() = true;

            /*
             * Delete the children of this state.
             */
            while( !_currentState->children().empty() )
            {
                delete _currentState->rChildren().back();
            }

            /*
             * Delete the conflict sets of this state.
             */
            _currentState->rConflictSets().clear();

            /*
             * Delete the conditions of this state.
             */
            while( !_currentState->conditions().empty() )
            {
                vs::Condition* rpCond = _currentState->rConditions().back();
                _currentState->rConditions().pop_back();
                delete rpCond;
            }

            /*
             * Delete the everything in oldConditions.
             */
            while( !oldConditions.empty() )
            {
                vs::Condition* rpCond = oldConditions.back();
                oldConditions.pop_back();
                delete rpCond;
            }

            /*
             * Delete the everything in disjunctionsOfCondConj.
             */
            while( !disjunctionsOfCondConj.empty() )
            {
                while( !disjunctionsOfCondConj.back().empty() )
                {
                    while( !disjunctionsOfCondConj.back().back().empty() )
                    {
                        vs::Condition* rpCond = disjunctionsOfCondConj.back().back().back();
                        disjunctionsOfCondConj.back().back().pop_back();
                        delete rpCond;
                    }
                    disjunctionsOfCondConj.back().pop_back();
                }
                disjunctionsOfCondConj.pop_back();
            }
            return false;
        }
        else
        {
            disjunctionsOfCondConj.push_back( DisjunctionOfConditionConjunctions() );
            disjunctionsOfCondConj.back().push_back( oldConditions );
            _currentState->addSubstitutionResults( disjunctionsOfCondConj );
            if( !_currentState->isInconsistent() )
            {
                insertDTinRanking( _currentState );
            }
            if( debug )
            {
                _currentState->print( "   ", cout );
            }
            return true;
        }
    }

    /**
     * Applies the most recent substitutions resp. of each of _currentState to all conditions,
     * which were recently added to _currentState.
     *
     * @param _currentState The currently considered state.
     */
    void VSModule::propagateNewConditions( State* _currentState )
    {
        if( debugmethods )
        {
            cout << __func__ << endl;
        }
        eraseDTsOfRanking( *_currentState );
        _currentState->rHasRecentlyAddedConditions() = false;

        /*
         * Collect the recently added conditions and mark them as not recently added.
         */
        bool deleteExistingTestCandidates = false;
        ConditionVector recentlyAddedConditions = ConditionVector();
        for( ConditionVector::iterator cond = _currentState->rConditions().begin(); cond != _currentState->conditions().end(); ++cond )
        {
            if( (**cond).recentlyAdded() )
            {
                (**cond).rRecentlyAdded() = false;
                recentlyAddedConditions.push_back( *cond );
                if( _currentState->pOriginalCondition() == NULL )
                {
                    if( (**cond).constraint().hasFinitelyManySolutionsIn( _currentState->index() ))
                    {
                        deleteExistingTestCandidates = true;
                    }
                }
            }
        }

        insertDTinRanking( _currentState );

        if( !_currentState->children().empty() )
        {
            if( deleteExistingTestCandidates || _currentState->initIndex( mAllVariables ))
            {
                _currentState->initConditionFlags();

                /*
                 * If the recently added conditions make another variable being the best to eliminate next
                 * delete all children.
                 */
                while( !_currentState->children().empty() )
                {
                    delete _currentState->rChildren().back();
                }
            }
            else
            {
                bool newTestCandidatesGenerated = false;
                if( _currentState->pOriginalCondition() == NULL )
                {
                    /*
                     * Check if there are new conditions in this state, which would have been better choices
                     * to generate test candidates than those conditions of the already generated test
                     * candidates. If so, generate the test candidates of the better conditions.
                     */
                    for( ConditionVector::iterator cond = recentlyAddedConditions.begin(); cond != recentlyAddedConditions.end(); ++cond )
                    {
                        if( (**cond).constraint().hasVariable( _currentState->index() ))
                        {
                            bool                  worseConditionFound = false;
                            StateVector::iterator child               = _currentState->rChildren().begin();
                            while( !worseConditionFound && child != _currentState->children().end() )
                            {
                                if( (**child).substitution().type() != ST_MINUS_INFINITY )
                                {
                                    ConditionSet::iterator oCond = (**child).rSubstitution().rOriginalConditions().begin();
                                    while( !worseConditionFound && oCond != (**child).substitution().originalConditions().end() )
                                    {
                                        if( (**cond).rConstraint().valuate( _currentState->index(), mAllVariables.size(), true )
                                                > (**oCond).rConstraint().valuate( _currentState->index(), mAllVariables.size(), true ))
                                        {
                                            newTestCandidatesGenerated = true;
                                            if( debug )
                                            {
                                                cout << "*** Eliminate " << _currentState->index() << " in ";
                                                (**cond).constraint().print( cout );
                                                cout << " creates:" << endl;
                                            }
                                            eliminate( _currentState, _currentState->index(), *cond );
                                            if( debug )
                                            {
                                                cout << "*** Eliminate ready." << endl;
                                            }
                                            worseConditionFound = true;
                                        }
                                        ++oCond;
                                    }
                                }
                                ++child;
                            }
                        }
                    }
                }

                /*
                 * Otherwise, add the recently added conditions to each child of the considered state to
                 * which a substitution must be or already has been applied.
                 */
                for( StateVector::iterator child = _currentState->rChildren().begin(); child != _currentState->children().end(); ++child )
                {
                    if( (**child).stateType() != SUBSTITUTION_TO_APPLY || (**child).isInconsistent() )
                    {
                        /*
                         * Apply substitution to new conditions and add the result to the substitution result vector.
                         */
                        substituteAll( *child, recentlyAddedConditions );
                        if( (**child).isInconsistent() &&!(**child).subResultsSimplified() )
                        {
                            (**child).simplify();
                            if( !(**child).conflictSets().empty() )
                            {
                                insertDTinRanking( *child );
                            }
                        }
                    }
                    else
                    {
                        if( newTestCandidatesGenerated )
                        {
                            insertDTinRanking( *child );
                            if( !(**child).children().empty() )
                            {
                                (**child).rHasChildrenToInsert() = true;
                            }
                        }
                        else
                        {
                            insertDTsinRanking( *child );
                        }
                    }
                }
            }
        }
    }

    /**
     * Increases the ID to allocate.
     */
    void VSModule::increaseIDCounter()
    {
        if( mIDCounter == MAX_ID )
        {
            mIDCounter = 1;
            cout << "Warning: Already allocated last ID." << endl;
        }
        else
        {
            mIDCounter++;
        }
    }

    /**
     * Inserts a state in the ranking.
     *
     * @param _state The states, which will be inserted.
     */
    void VSModule::insertDTinRanking( State* _state )
    {
        if( debugmethods )
        {
            cout << __func__ << endl;
        }
        if( !_state->markedAsDeleted() &&!(_state->isInconsistent() && _state->conflictSets().empty() && _state->conditionsSimplified()))
        {
            if( _state->id() != 0 )
            {
                unsigned id = _state->id();
                eraseDTofRanking( *_state );
                _state->setID( id );
            }
            else
            {
                increaseIDCounter();
                _state->setID( mIDCounter );
            }

            _state->updateValuation();

            if( (mpRanking->insert( ValStatePair( _state->valuationPlusID(), _state ))).second == false )
            {
                cout << "Warning: Could not insert. Entry already exists.";
                cout << endl;
            }
        }
    }

    /**
     * Inserts a state and all its successors in the ranking.
     *
     * @param _state The root of the states, which will be inserted.
     */
    void VSModule::insertDTsinRanking( State* _state )
    {
        if( debugmethods )
        {
            cout << __func__ << endl;
        }
        insertDTinRanking( _state );

        if( _state->conditionsSimplified() && _state->subResultsSimplified() )
        {
            for( StateVector::iterator dt = (*_state).rChildren().begin(); dt != (*_state).children().end(); ++dt )
            {
                insertDTsinRanking( *dt );
            }
        }
    }

    /**
     * Erases a state of the ranking.
     *
     * @param _state The states, which will be deleted.
     *
     * @return  True, if the state was in the ranking.
     */
    bool VSModule::eraseDTofRanking( State& _state )
    {
        if( debugmethods )
        {
            cout << __func__ << endl;
        }
        ValuationMap::iterator valDTPair = (*mpRanking).find( _state.valuationPlusID() );
        if( valDTPair != (*mpRanking).end() )
        {
            (*mpRanking).erase( valDTPair );
            _state.setID( 0 );
            return true;
        }
        else
        {
            return false;
        }
    }

    /**
     * Erases a state and its sucessors of the ranking.
     *
     * @param _state The root of the states, which will be deleted.
     */
    void VSModule::eraseDTsOfRanking( State& _state )
    {
        if( debugmethods )
        {
            cout << __func__ << endl;
        }
        eraseDTofRanking( _state );

        for( StateVector::iterator dt = _state.rChildren().begin(); dt != _state.children().end(); ++dt )
        {
            eraseDTsOfRanking( **dt );
        }
    }

    /**
     * Update the infeasible subset. It is not empty, if the set of received constraints is inconsistent.
     */
    void VSModule::updateInfeasibleSubset()
    {
        if( debugmethods )
        {
            cout << __func__ << endl;
        }
#ifdef VS_INFEASIBLE_SUBSET_GENERATION

        /*
         * Determine the minimum covering sets of the conflict sets, i.e. the infeasible subsets
         * of the root.
         */
        ConditionSetSet minCoverSets = ConditionSetSet();
        ConditionSetSetSet confSets  = ConditionSetSetSet();
        ConflictSets::iterator nullConfSet = mpStateTree->rConflictSets().find( NULL );
        if( nullConfSet != mpStateTree->rConflictSets().end() )
        {
            confSets.insert( nullConfSet->second.begin(), nullConfSet->second.end() );
        }
        else
        {
            for( ConflictSets::iterator confSet = mpStateTree->rConflictSets().begin(); confSet != mpStateTree->rConflictSets().end(); ++confSet )
            {
                confSets.insert( confSet->second.begin(), confSet->second.end() );
            }
        }
        allMinimumCoveringSets( confSets, minCoverSets );
        /*
         * Get the smallest infeasible subset.
         */
        ConditionSetSet::const_iterator smallestMinCoverSet = minCoverSets.begin();

        if( smallestMinCoverSet != minCoverSets.end() )
        {
            ConditionSetSet::const_iterator minCoverSet = minCoverSets.begin();
            minCoverSet++;
            while( minCoverSet != minCoverSets.end() )
            {
                /*
                 * The infeasible subset is smaller than the globally stored one.
                 */
                if( (*minCoverSet).size() < (*smallestMinCoverSet).size() )
                {
                    smallestMinCoverSet = minCoverSet;
                }
                minCoverSet++;
            }

            /*
             * Change the globally stored infeasible subset to the smaller one.
             */
            mInfeasibleSubsets.clear();
            mInfeasibleSubsets.push_back( set< const Formula* >() );
            for( ConditionSet::const_iterator cond = (*smallestMinCoverSet).begin(); cond != (*smallestMinCoverSet).end(); ++cond )
            {
                for( ConditionSet::const_iterator oCond = (**cond).originalConditions().begin();
                	 oCond != (**cond).originalConditions().end();
                     ++oCond )
                {
                    Formula::const_iterator receivedConstraint = receivedFormulaBegin();
                    while( receivedConstraint != receivedFormulaEnd() )
                    {
                        if( (**oCond).constraint() == (*receivedConstraint)->constraint() )
                        {
                            break;
                        }
                        receivedConstraint++;
                    }

                    if( receivedConstraint == receivedFormulaEnd() )
                    {
                        cout << "BLA1" << endl;
                        printAll( cout );
                        assert( false );
                    }

                    mInfeasibleSubsets.back().insert( *receivedConstraint );
                }
            }
        }
        else
        {
            /*
             * Set the infeasible subset to the set of all received constraints.
             */
            mInfeasibleSubsets.push_back( set< const Formula* >() );
            for( Formula::const_iterator cons = receivedFormulaBegin();
            	 cons != receivedFormulaEnd();
            	 ++cons )
            {
            	mInfeasibleSubsets.back().insert( *cons );
            }
        }
#else
        /*
         * Set the infeasible subset to the set of all received constraints.
         */
        mInfeasibleSubsets.push_back( set< const Formula* >() );
        for( Formula::const_iterator cons = receivedFormulaBegin();
        	 cons != receivedFormulaEnd();
        	 ++cons )
        {
        	mInfeasibleSubsets.back().insert( *cons );
        }
#endif
    }

    /**
     * Resets everything in the solver except of the received constraints and the backtrack point history.
     */
    void VSModule::reset()
    {
        if( debugmethods )
        {
            cout << __func__ << endl;
        }

        /*
         * Delete everything but the received constraints and their variables including
         * the variable valuations.
         */
        delete mpRanking;
        delete mpStateTree;

        /*
         * Initialize everything but the received constraints and their variablesincluding
         * the variable valuations.
         */
        mInconsistentConstraintAdded = false;
        mIDCounter                   = 0;
        mInfeasibleSubsets.clear();
        mpStateTree = new State();
        mpRanking   = new ValuationMap();

        while( !mReceivedConstraintsAsConditions.empty() )
        {
            vs::Condition* pRecCond = mReceivedConstraintsAsConditions.begin()->second;
            mReceivedConstraintsAsConditions.erase( mReceivedConstraintsAsConditions.begin() );
            delete pRecCond;
        }

        Formula::const_iterator          cons = receivedFormulaBegin();
        while( cons != receivedFormulaEnd() )
        {
			vs::Condition* condition = new vs::Condition( (*cons)->constraint() );
			mReceivedConstraintsAsConditions[(*cons)->pConstraint()] = condition;

            /*
             * Check the consistency of the constraint to add.
             */
            unsigned isConstraintConsistent = (*cons)->constraint().isConsistent();

            /*
             * Clear the ranking.
             */
            if( isConstraintConsistent != 1 )
            {
                eraseDTsOfRanking( *mpStateTree );
                mIDCounter = 0;

                /*
                 * Add the variables of the new constraint to the history of all occured variables.
                 */
                if( isConstraintConsistent == 2 )
                {
                    //              mpStateTree->rConditions().push_back( new Condition( **cons, 0 ) );
                    //              (*(mpStateTree->rConditions()).back()).rRecentlyAdded() = true;
                    //              mpStateTree->rConditions().back()->rOriginalConditions().insert( cond->second );

                    ConditionSet oConds = ConditionSet();
                    oConds.insert( condition );

                    vector<DisjunctionOfConditionConjunctions> subResults = vector<DisjunctionOfConditionConjunctions>();
                    DisjunctionOfConditionConjunctions subResult = DisjunctionOfConditionConjunctions();
                    ConditionVector condVector                   = ConditionVector();
                    condVector.push_back( new vs::Condition( (*cons)->constraint(), false, oConds, 0 ));
                    subResult.push_back( condVector );
                    subResults.push_back( subResult );
                    mpStateTree->addSubstitutionResults( subResults );

                    mpStateTree->rHasRecentlyAddedConditions() = true;
                    insertDTinRanking( mpStateTree );
                }
                else if( isConstraintConsistent == 0 )
                {
                    mInconsistentConstraintAdded = true;
                }
            }
            cons++;
        }
    }

    /**
     * Finds all minimum covering sets of a vector of sets of sets. A minimum covering set
     * fulfills the following properties:
     *
     *          1.) It covers in each set of sets at least one of its sets.
     *          2.) If you delete any element of the minimum covering set, the
     *              first property does not hold anymore.
     *
     * @param _conflictSets     The vector of sets of sets, for which the method finds all minimum covering sets.
     * @param _minCovSets   The resulting minimum covering sets.
     */
    void VSModule::allMinimumCoveringSets( const ConditionSetSetSet& _conflictSets, ConditionSetSet& _minCovSets )
    {
        if( !_conflictSets.empty() )
        {
            /*
             * First we construct all possible combinations of combining all single sets of each set of sets.
             * Store for each set an iterator.
             */
            vector<ConditionSetSet::iterator> conditionSetSetIters = vector<ConditionSetSet::iterator>();
            for( ConditionSetSetSet::const_iterator conflictSet = _conflictSets.begin(); conflictSet != _conflictSets.end(); ++conflictSet )
            {
                conditionSetSetIters.push_back( (*conflictSet).begin() );

                /*
                 * Assure, that the set is not empty.
                 */
                assert( conditionSetSetIters.back() != (*conflictSet).end() );
            }
            ConditionSetSetSet::iterator                conflictSet;
            vector<ConditionSetSet::iterator>::iterator conditionSet;

            /*
             * Find all covering sets by forming the union of all combinations.
             */
            bool lastCombinationReached = false;
            while( !lastCombinationReached )
            {
                /*
                 * Create a new combination of vectors.
                 */
                ConditionSet coveringSet = ConditionSet();

                bool previousIteratorIncreased = false;

                /*
                 * For each set of sets in the vector of sets of sets, choose a set in it. We combine
                 * these sets by forming their union and store it as a covering set.
                 */
                conditionSet = conditionSetSetIters.begin();
                conflictSet  = _conflictSets.begin();

                while( conditionSet != conditionSetSetIters.end() )
                {
                    if( (*conflictSet).empty() )
                    {
                        conflictSet++;
                        conditionSet++;
                    }
                    else
                    {
                        coveringSet.insert( (**conditionSet).begin(), (**conditionSet).end() );

                        /*
                         * Set the iterator.
                         */
                        if( !previousIteratorIncreased )
                        {
                            (*conditionSet)++;
                            if( *conditionSet != (*conflictSet).end() )
                            {
                                previousIteratorIncreased = true;
                            }
                            else
                            {
                                *conditionSet = (*conflictSet).begin();
                            }
                        }
                        conflictSet++;
                        conditionSet++;
                        if( !previousIteratorIncreased && conditionSet == conditionSetSetIters.end() )
                        {
                            lastCombinationReached = true;
                        }
                    }
                }
                _minCovSets.insert( coveringSet );
            }

            /*
             * Delete all covering sets, which are not minimal. We benefit of the set of sets property,
             * which sorts its sets according to the elements they contain. If a set M is a subset of
             * another set M', the position of M in the set of sets is before M'.
             */
            ConditionSetSet::iterator minCoverSet = _minCovSets.begin();
            ConditionSetSet::iterator coverSet    = _minCovSets.begin();
            coverSet++;

            while( coverSet != _minCovSets.end() )
            {
                ConditionSet::iterator cond1 = (*minCoverSet).begin();
                ConditionSet::iterator cond2 = (*coverSet).begin();
                while( cond1 != (*minCoverSet).end() && cond2 != (*coverSet).end() )
                {
                    if( *cond1 != *cond2 )
                    {
                        break;
                    }
                    cond1++;
                    cond2++;
                }
                if( cond1 == (*minCoverSet).end() )
                {
                    _minCovSets.erase( coverSet++ );
                }
                else
                {
                    minCoverSet = coverSet;
                    coverSet++;
                }
            }
        }
    }

    /**
     * Run the backend solvers on the conditions of the given state.
     *
     * @param _state    The state to check the conditions of.
     *
     * @return  TS_True,    if the conditions are consistent and there is no unfinished ancestor;
     *          TS_False,   if the conditions are inconsistent;
     *          TS_Unknown, if the theory solver cannot give an answer for these conditons.
     */
    Answer VSModule::runBackendSolvers( State* _state )
    {
#ifdef VS_DEBUG_METHODS
        cout << __func__ << endl;
#endif

        /*
         * Run the backends on the constraint of the state.
         */
        for( unsigned pos = 0; pos < passedFormulaSize(); ++pos )
        {
            removeSubformulaFromPassedFormula( pos );
        }
        for( ConditionVector::const_iterator cond = _state->conditions().begin(); cond != _state->conditions().end(); ++cond )
        {
            vec_set_const_pFormula origins = vec_set_const_pFormula();
            addSubformulaToPassedFormula( new Formula( (**cond).pConstraint() ), origins );
        }

        switch( runBackends() )
        {
            case True:
            {
                State * unfinishedAncestor;
                if( _state->unfinishedAncestor( unfinishedAncestor ))
                {
                    /*
                     * Go back to this ancestor and refine.
                     */
                    eraseDTsOfRanking( *unfinishedAncestor );
                    unfinishedAncestor->extendSubResultCombination();
                    unfinishedAncestor->rStateType() = COMBINE_SUBRESULTS;
                    if( unfinishedAncestor->refreshConditions() )
                    {
                        insertDTinRanking( unfinishedAncestor );
                    }
                    else
                    {
                        insertDTsinRanking( unfinishedAncestor );
                    }
                }
                return True;
            }
            case False:
            {
                /*
                 * Get the conflict sets formed by the infeasible subsets in the backend.
                 */
                ConditionSetSet conflictSet = ConditionSetSet();
                for( vec_set_const_pFormula::const_iterator infSubSet = mInfeasibleSubsets.begin();
                     infSubSet != mInfeasibleSubsets.end();
                     ++infSubSet )
                {
                    ConditionSet conflict = ConditionSet();
                    for( set< const Formula* >::const_iterator subformula = infSubSet->begin(); subformula != infSubSet->end(); ++subformula )
                    {
                        for( ConditionVector::const_iterator cond = _state->conditions().begin(); cond != _state->conditions().end(); ++cond )
                        {
                            if( (*cond)->pConstraint() == (*subformula)->pConstraint() )
                            {
                                conflict.insert( *cond );
                                break;
                            }
                        }
                    }
                    conflictSet.insert( conflict );
                }
                _state->addConflictSet( NULL, conflictSet );
                eraseDTsOfRanking( *_state );

                /*
                 * If the considered state is the root, update the found infeasible subset as infeasible subset.
                 */
                if( _state->isRoot() )
                {
                    updateInfeasibleSubset();
                }
                /*
                 * If the considered state is not the root, pass the infeasible subset to the father.
                 */
                else
                {
                    if( _state->passConflictToFather() )
                    {
                        insertDTinRanking( _state );
                    }
                    else
                    {
                        eraseDTsOfRanking( _state->rFather() );
                        insertDTinRanking( _state->pFather() );
                    }
                }
                return False;
            }
            case Unknown:
            {
                return Unknown;
            }
            default:
            {
                cerr << "Unknown answer type!" << endl;
                assert( false );
                return Unknown;
            }
        }
    }

    vec_set_const_pFormula VSModule::getOriginsOfCondition( const vs::Condition* _condition, const vs::State* _state ) const
    {
        vec_set_const_pFormula result = vec_set_const_pFormula();
        set< const vs::Condition* > currentOrigins = set< const vs::Condition* >();
        currentOrigins.insert( _condition );
        set< const vs::Condition* > currentOriginsOrigins = set< const vs::Condition* >();
        const State* currentState = _state;
        while( !currentState->isRoot() )
        {
            currentOriginsOrigins.clear();
            for( set< const vs::Condition* >::iterator ocond = currentOrigins.begin();
                 ocond != currentOrigins.end();
                 ++ocond )
            {
                if( (*ocond)->originalConditions().empty() )
                {
                    currentOriginsOrigins.insert( currentState->pOriginalCondition() );
                }
                else
                {
                    currentOriginsOrigins.insert( (*ocond)->originalConditions().begin(), (*ocond)->originalConditions().end() );
                }
            }
            currentOrigins = currentOriginsOrigins;
            currentState = currentState->pFather();
        }

        return result;
    }

    /**
     * Prints the history to the output stream.
     *
     * @param _out The output stream where the history should be printed.
     */
    void VSModule::printAll( ostream& _out ) const
    {
        _out << "*** Current solver status, where the constraints" << endl;
        for( ConstraintConditionMap::const_iterator cond = mReceivedConstraintsAsConditions.begin();
        	 cond != mReceivedConstraintsAsConditions.end();
        	 ++cond )
        {
            _out << "***    ";
            cond->first->print( _out );
            _out << " <-> ";
            cond->second->print( _out );
            _out << endl;
        }
        _out << "*** have been added:" << endl;

        _out << "*** mInconsistentConstraintAdded: " << mInconsistentConstraintAdded << endl;
        _out << "*** mIDCounter: " << mIDCounter << endl;
        printRanking( cout );

        _out << "*** State tree:" << endl;
        mpStateTree->print( "   ", _out );
    }

    /**
     * Prints the history to the output stream.
     *
     * @param _out The output stream where the history should be printed.
     */
    void VSModule::printRanking( ostream& _out ) const
    {
        _out << "*** Current ranking:" << endl;
        unsigned counter = 0;
        for( ValuationMap::const_iterator valDTPair = (*mpRanking).begin(); valDTPair != (*mpRanking).end(); ++valDTPair )
        {
            counter++;
            (*(*valDTPair).second).printAlone( "   ", _out );
            if( counter > 10 )
            {
                break;
            }
        }
    }

    /**
     * Prints the answer if existent.
     *
     * @param _out The output stream where the answer should be printed.
     */
    void VSModule::printAnswer( ostream& _out ) const
    {
        _out << "*** Answer:" << endl;
        if( (*mpRanking).empty() )
        {
            _out << "***        False." << endl;
        }
        else
        {
            _out << "***        True:" << endl;
            const State* currentState = (*(*mpRanking).begin()).second;
            while( !(*currentState).isRoot() )
            {
                _out << "***           " << (*currentState).substitution().toString2() << endl;
                currentState = (*currentState).pFather();
            }
        }
        _out << endl;
    }

}    // end namespace smtrat

