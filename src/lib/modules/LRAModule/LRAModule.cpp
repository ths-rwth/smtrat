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
 * along with SMT-RAT.  If not, see <http://www.gnrg/licenses/>.
 *
 */
/*
 * File:   LRAModule.cpp
 * @author name surname <emailadress>
 *
 * @version 2012-04-05
 * Created on April 5th, 2012, 3:22 PM
 */


#include "LRAModule.h"
#include <iostream>

//#define DEBUG_LRA_MODULE
//#define LRA_TERMINATION_INVARIANCE
#define LRA_SIMPLE_THEORY_PROPAGATION
#define LRA_SIMPLE_CONFLICT_SEARCH
#define LRA_ONE_REASON
//#define LRA_RESTORE_PREVIOUS_CONSISTENT_ASSIGNMENT
//#define LRA_EARLY_BRANCHING
#ifndef LRA_GOMORY_CUTS
#ifndef LRA_CUTS_FROM_PROOFS
#endif
#endif

using namespace std;
using namespace smtrat::lra;

namespace smtrat
{
    LRAModule::LRAModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* const _manager ):
        Module( _type, _formula, _conditionals, _manager ),
        mInitialized( false ),
        mAssignmentFullfilsNonlinearConstraints( false ),
        mStrongestBoundsRemoved( false ),
        mProbableLoopCounter( 0 ),
        mTableau( mpPassedFormula->end() ),
        mLinearConstraints(),
        mNonlinearConstraints(),
        mActiveResolvedNEQConstraints(),
        mActiveUnresolvedNEQConstraints(),
        mResolvedNEQConstraints(),
        mDelta( newAuxiliaryRealVariable( "delta_" + to_string( id() ) ) ),
        mBoundCandidatesToPass()
    {
        #ifdef SMTRAT_DEVOPTION_Statistics
        stringstream s;
        s << moduleName( type() ) << "_" << id();
        mpStatistics = new LRAModuleStatistics( s.str() );
        #endif
    }

    LRAModule::~LRAModule()
    {
        #ifdef SMTRAT_DEVOPTION_Statistics
        delete mpStatistics;
        #endif
    }

    /**
     * Informs this module about the existence of the given constraint, which means
     * that it could be added in future.
     *
     * @param _constraint The constraint to inform about.
     * @return False, if the it can be determined that the constraint itself is conflicting;
     *         True,  otherwise.
     */
    bool LRAModule::inform( const Constraint* const _constraint )
    {
        #ifdef DEBUG_LRA_MODULE
        cout << "LRAModule::inform  " << "inform about " << *_constraint << endl;
        #endif
        Module::inform( _constraint );
        if( !_constraint->lhs().isConstant() && _constraint->lhs().isLinear() )
        {
            bool elementInserted = mLinearConstraints.insert( _constraint ).second;
            if( elementInserted )
            {
                setBound( _constraint );
            }
        }
        return _constraint->isConsistent() != 0;
    }

    /**
     *
     * Adds a sub-formula/constraint to the so far received sub-formula/constraints.
     *
     * @param _subformula The position of the constraint within the received constraints.
     * @return False, if a conflict is detected;
     *         True,  otherwise.
     */
    bool LRAModule::assertSubformula( list<const Formula*>::const_iterator _subformula )
    {
        #ifdef DEBUG_LRA_MODULE
        cout << "LRAModule::assertSubformula  " << "add " << **_subformula << "(" << *_subformula << ")" << endl;
        #endif
        Module::assertSubformula( _subformula );
        switch( (*_subformula)->getType() )
        {
            case FFALSE:
            {
                PointerSet<Formula> infSubSet;
                infSubSet.insert( *_subformula );
                mInfeasibleSubsets.push_back( infSubSet );
                foundAnswer( False );
                #ifdef SMTRAT_DEVOPTION_Statistics
                mpStatistics->addConflict( mInfeasibleSubsets );
                #endif
                return false;
            }
            case TTRUE:
            {
                return true;
            }
            case CONSTRAINT:
            {
                const Constraint* constraint  = (*_subformula)->pConstraint();
                #ifdef SMTRAT_DEVOPTION_Statistics
                mpStatistics->add( *constraint );
                #endif
                unsigned consistency = constraint->isConsistent();
                if( consistency == 2 )
                {
                    mAssignmentFullfilsNonlinearConstraints = false;
                    if( constraint->lhs().isLinear() )
                    {
//                        bool elementInserted = mLinearConstraints.insert( constraint ).second;
//                        if( elementInserted && mInitialized )
//                        {
//                            mTableau.newBound( constraint );
//                        }
                        if( constraint->relation() != Relation::NEQ )
                        {
                            auto constrBoundIter = mTableau.constraintToBound().find( constraint );
                            assert( constrBoundIter != mTableau.constraintToBound().end() );
                            const vector< const LRABound* >* bounds = constrBoundIter->second;
                            assert( bounds != NULL );
                            PointerSet<Formula> originSet;
                            originSet.insert( *_subformula );
                            activateBound( *bounds->begin(), originSet );

                            if( (*bounds->begin())->neqRepresentation() != NULL )
                            {
                                auto pos = mActiveUnresolvedNEQConstraints.find( (*bounds->begin())->neqRepresentation() );
                                if( pos != mActiveUnresolvedNEQConstraints.end() )
                                {
                                    auto entry = mActiveResolvedNEQConstraints.insert( *pos );
                                    removeSubformulaFromPassedFormula( pos->second.position );
                                    entry.first->second.position = mpPassedFormula->end();
                                    mActiveUnresolvedNEQConstraints.erase( pos );
                                }
                            }
                            return mInfeasibleSubsets.empty();
                        }
                        else
                        {
                            auto constrBoundIter = mTableau.constraintToBound().find( constraint );
                            assert( constrBoundIter != mTableau.constraintToBound().end() );
                            const vector< const LRABound* >* bounds = constrBoundIter->second;
                            assert( bounds != NULL );
                            assert( bounds->size() >= 4 );
                            if( (*bounds)[0]->isActive() || (*bounds)[1]->isActive() || (*bounds)[2]->isActive() || (*bounds)[3]->isActive() )
                            {
                                Context context = Context();
                                context.origin = *_subformula;
                                context.position = mpPassedFormula->end();
                                mActiveResolvedNEQConstraints.insert( pair< const Constraint*, Context >( constraint, context ) );
                                if( (*bounds)[1]->isActive() || (*bounds)[2]->isActive() )
                                {
                                    int numA = (*bounds)[1]->isActive() ? 1 : 2;
                                    int numB = (*bounds)[1]->isActive() ? 0 : 3;
                                    PointerSet<Formula> involvedConstraints;
                                    PointerSet<Formula> originSet;
                                    originSet.insert( *_subformula );
                                    auto iter = (*bounds)[numA]->origins().begin();
                                    assert( iter != (*bounds)[numA]->origins().end() );
                                    originSet.insert( iter->begin(), iter->end() );
                                    involvedConstraints.insert( iter->begin(), iter->end() );
                                    activateBound( (*bounds)[numB], originSet );
                                    ++iter;
                                    while( iter != (*bounds)[numA]->origins().end() )
                                    {
                                        PointerSet<Formula> originSetB;
                                        originSetB.insert( *_subformula );
                                        originSetB.insert( iter->begin(), iter->end() );
                                        involvedConstraints.insert( iter->begin(), iter->end() );
                                        (*bounds)[numB]->pOrigins()->push_back( std::move( originSetB ) );
                                        ++iter;
                                    }
                                    for( const Formula* fconstraint : involvedConstraints )
                                    {
                                        auto constrBoundIter = mTableau.rConstraintToBound().find( fconstraint->pConstraint() );
                                        assert( constrBoundIter != mTableau.constraintToBound().end() );
                                        vector< const LRABound* >* constraintToBounds = constrBoundIter->second;
                                        constraintToBounds->push_back( (*bounds)[numB] );
                                    }
                                }
                            }
                            else
                            {
                                addSubformulaToPassedFormula( newFormula( constraint ), *_subformula ); // TODO: maybe not necessary to create this formula every time, store it instead an reuse it
                                Context context = Context();
                                context.origin = *_subformula;
                                context.position = --mpPassedFormula->end();
                                mActiveUnresolvedNEQConstraints.insert( pair< const Constraint*, Context >( constraint, context ) );
                            }
                        }
                    }
                    else
                    {
                        addSubformulaToPassedFormula( *_subformula, *_subformula );
                        mNonlinearConstraints.insert( constraint );
                        return true;
                    }
                }
            }
            default:
                return true;
        }
        return true;
    }

    /**
     * Removes a sub-formula/constraint of the so far received sub-formula/constraints.
     *
     * @param _subformula The position of the constraint within the received constraints.
     */
    void LRAModule::removeSubformula( ModuleInput::const_iterator _subformula )
    {
        #ifdef DEBUG_LRA_MODULE
        cout << "remove " << **_subformula << "(" << *_subformula << ")" << endl;
        #endif
        if( (*_subformula)->getType() == CONSTRAINT )
        {
            // Remove the mapping of the constraint to the sub-formula in the received formula
            const Constraint* constraint = (*_subformula)->pConstraint();
            #ifdef SMTRAT_DEVOPTION_Statistics
            mpStatistics->remove( *constraint );
            #endif
            if( constraint->isConsistent() == 2 )
            {
                if( constraint->lhs().isLinear() )
                {
                    // Deactivate the bounds regarding the given constraint
                    auto constrBoundIter = mTableau.constraintToBound().find( constraint );
                    assert( constrBoundIter != mTableau.rConstraintToBound().end() );
                    vector< const LRABound* >* bounds = constrBoundIter->second;
                    assert( bounds != NULL );
                    auto bound = bounds->begin();
                    int pos = 0;
                    int dontRemoveBeforePos = (*_subformula)->constraint().relation() == Relation::NEQ ? 4 : 1;
                    while( bound != bounds->end() )
                    {
                        if( !(*bound)->origins().empty() )
                        {
                            auto originSet = (*bound)->pOrigins()->begin();
                            bool mainOriginRemains = true;
                            while( originSet != (*bound)->origins().end() )
                            {
                                if( originSet->find( *_subformula ) != originSet->end() && (mainOriginRemains || originSet->size() > 1) )
                                {
                                    originSet = (*bound)->pOrigins()->erase( originSet );
                                    if( originSet->size() == 1 ) mainOriginRemains = false; // ensures that only one main origin is removed, in the case that a formula is contained more than once in the module input
                                }
                                else
                                {
                                    ++originSet;
                                }
                            }
                            if( (*bound)->origins().empty() )
                            {
                                if( (*bound)->neqRepresentation() != NULL )
                                {
                                    auto constrBoundIterB = mTableau.constraintToBound().find( (*bound)->neqRepresentation() );
                                    assert( constrBoundIterB != mTableau.constraintToBound().end() );
                                    const vector< const LRABound* >* uebounds = constrBoundIterB->second;
                                    assert( uebounds != NULL );
                                    assert( uebounds->size() >= 4 );
                                    if( !(*uebounds)[0]->isActive() && !(*uebounds)[1]->isActive() && !(*uebounds)[2]->isActive() && !(*uebounds)[3]->isActive() )
                                    {
                                        auto pos = mActiveResolvedNEQConstraints.find( (*bound)->neqRepresentation() );
                                        if( pos != mActiveResolvedNEQConstraints.end() )
                                        {
                                            auto entry = mActiveUnresolvedNEQConstraints.insert( *pos );
                                            mActiveResolvedNEQConstraints.erase( pos );
                                            addSubformulaToPassedFormula( newFormula( entry.first->first ), entry.first->second.origin );
                                            entry.first->second.position = --mpPassedFormula->end();
                                        }
                                    }
                                }
                                LRAVariable& var = *(*bound)->pVariable();
                                #ifdef LRA_RESTORE_PREVIOUS_CONSISTENT_ASSIGNMENT
                                if( var.deactivateBound( *bound, mpPassedFormula->end() ) )
                                {
                                    mStrongestBoundsRemoved = true;
                                }
                                #else
                                if( var.deactivateBound( *bound, mpPassedFormula->end() ) && !var.isBasic() )
                                {
                                    if( var.supremum() < var.assignment() )
                                    {
                                        mTableau.updateBasicAssignments( var.position(), LRAValue( var.supremum().limit() - var.assignment() ) );
                                        var.rAssignment() = var.supremum().limit();
                                    }
                                    else if( var.infimum() > var.assignment() )
                                    {
                                        mTableau.updateBasicAssignments( var.position(), LRAValue( var.infimum().limit() - var.assignment() ) );
                                        var.rAssignment() = var.infimum().limit();
                                    }
                                }
                                #endif
                                if( !(*bound)->pVariable()->pSupremum()->isInfinite() )
                                {
                                    mBoundCandidatesToPass.push_back( (*bound)->pVariable()->pSupremum() );
                                }
                                if( !(*bound)->pVariable()->pInfimum()->isInfinite() )
                                {
                                    mBoundCandidatesToPass.push_back( (*bound)->pVariable()->pInfimum() );
                                }

                                if( !(*bound)->variable().isActive() && (*bound)->variable().isBasic() && !(*bound)->variable().isOriginal() )
                                {
                                    mTableau.deactivateBasicVar( (*bound)->pVariable() );
                                }
                            }
                        }
                        if( (*bound)->origins().empty() && pos >= dontRemoveBeforePos )
                            bound = bounds->erase( bound );
                        else
                        {
                            ++bound;
                            ++pos;
                        }
                    }
                    if( (*_subformula)->constraint().relation() == Relation::NEQ )
                    {
                        if( mActiveResolvedNEQConstraints.erase( (*_subformula)->pConstraint() ) == 0 )
                        {
                            auto iter = mActiveUnresolvedNEQConstraints.find( (*_subformula)->pConstraint() );
                            if( iter != mActiveUnresolvedNEQConstraints.end() )
                            {
                                removeSubformulaFromPassedFormula( iter->second.position );
                                mActiveUnresolvedNEQConstraints.erase( iter );
                            }
                        }
                    }
                }
                else
                {
                    auto nonLinearConstraint = mNonlinearConstraints.find( constraint );
                    assert( nonLinearConstraint != mNonlinearConstraints.end() );
                    mNonlinearConstraints.erase( nonLinearConstraint );
                }
            }
        }
        Module::removeSubformula( _subformula );
    }

    /**
     * Checks the consistency of the so far received constraints.
     * @return true, if the so far received constraints are consistent;
     *         false, if the so far received constraints are inconsistent;
     *         unknown, if this module cannot determine whether the so far received constraints are consistent or not.
     */
    Answer LRAModule::isConsistent()
    {
        #ifdef DEBUG_LRA_MODULE
        cout << "check for consistency" << endl;
        printReceivedFormula();
        #endif
        Answer result = Unknown;
        #ifdef LRA_TERMINATION_INVARIANCE
        typedef pair<vector<const LRAVariable*>, vector<const LRAVariable*>> TableauConf;
        struct compTableaus
        {
            bool operator()( const TableauConf& _tcA, const TableauConf& _tcB ) const
            {
                auto iterA = _tcA.first.begin();
                auto iterB = _tcB.first.begin();
                while( iterA != _tcA.first.end() && iterB != _tcB.first.end() )
                {
                    if( *iterA < *iterB ) return true;
                    else if( *iterA > *iterB ) return false;
                    ++iterA;
                    ++iterB;
                }
                assert( iterA == _tcA.first.end() && iterB == _tcB.first.end() );
                iterA = _tcA.second.begin();
                iterB = _tcB.second.begin();
                while( iterA != _tcA.second.end() && iterB != _tcB.second.end() )
                {
                    if( *iterA < *iterB ) return true;
                    else if( *iterA > *iterB ) return false;
                    ++iterA;
                    ++iterB;
                }
                assert( iterA == _tcA.second.end() && iterB == _tcB.second.end() );
                return false;
            }
        };
        set<TableauConf, compTableaus> tcs;
        #endif
        if( !mpReceivedFormula->isConstraintConjunction() )
        {
            goto Return; // Unknown
        }
        if( !mInfeasibleSubsets.empty() )
        {
            result = False;
            goto Return;
        }
        #ifdef LRA_USE_PIVOTING_STRATEGY
        mTableau.setBlandsRuleStart( 1000 );//(unsigned) mTableau.columns().size() );
        #endif
        mTableau.compressRows();
        for( ; ; )
        {
            // Check whether a module which has been called on the same instance in parallel, has found an answer.
            if( anAnswerFound() )
            {
                result = Unknown;
                goto Return;
            }
            // Find a pivoting element in the tableau.
            #ifdef LRA_TERMINATION_INVARIANCE
            TableauConf tc;
            for( auto iter = mTableau.rows().begin(); iter != mTableau.rows().end(); ++iter )
                tc.first.push_back(iter->mName);
            for( auto iter = mTableau.columns().begin(); iter != mTableau.columns().end(); ++iter )
                tc.second.push_back(iter->mName);
            bool inserted = tcs.insert( tc ).second;
            if( inserted ) cout << "[LRA] non-termination" << endl;
            assert( inserted );
            #endif
            struct pair<EntryID,bool> pivotingElement = mTableau.nextPivotingElement();
//            cout << "\r" << mTableau.numberOfPivotingSteps() << endl;
            #ifdef DEBUG_LRA_MODULE
            if( pivotingElement.second && pivotingElement.first != LAST_ENTRY_ID )
            {
                cout << endl;
                mTableau.print( pivotingElement.first, cout, "    " );
                cout << endl;
            }
            #endif
            // If there is no conflict.
            if( pivotingElement.second )
            {
                // If no basic variable violates its bounds (and hence no variable at all).
                if( pivotingElement.first == 0 )
                {
                    #ifdef DEBUG_LRA_MODULE
                    mTableau.print();
                    mTableau.printVariables();
                    cout << "True" << endl;
                    #endif
                    // If the current assignment also fulfills the nonlinear constraints.
                    if( checkAssignmentForNonlinearConstraint() )
                    {
                        #ifdef LRA_GOMORY_CUTS 
                        if( gomory_cut() )
                            goto Return; // Unknown
                        #endif 
                        #ifdef LRA_CUTS_FROM_PROOFS
                        if( cuts_from_proofs() )
                            goto Return; // Unknown
                        #endif
                        if( branch_and_bound() )
                            goto Return; // Unknown
                        result = True;
                        #ifdef LRA_RESTORE_PREVIOUS_CONSISTENT_ASSIGNMENT
                        mTableau.storeAssignment();
                        #endif
                        goto Return;
                    }
                    // Otherwise, check the consistency of the formula consisting of the nonlinear constraints and the tightest bounds with the backends.
                    else
                    {
                        adaptPassedFormula();
                        Answer a = runBackends();
                        if( a == False )
                            getInfeasibleSubsets();
                        result = a;
                        goto Return;
                    }
                }
                else
                {
                    // Pivot at the found pivoting entry.
                    #ifdef LRA_EARLY_BRANCHING
                    LRAVariable* newBasicVar = mTableau.pivot( pivotingElement.first );
                    Rational ratAss = newBasicVar->assignment().mainPart().toRational();
                    if( newBasicVar->isActive() && newBasicVar->isInteger() && !carl::isInteger( ratAss ) )
                    {
                        if( !probablyLooping( newBasicVar->expression(), ratAss ) )
                        {
                            assert( newBasicVar->assignment().deltaPart() == 0 );
                            PointerSet<Formula> premises;
                            mTableau.collect_premises( newBasicVar, premises );                
                            branchAt( newBasicVar->expression(), ratAss, premises );
                            goto Return;
                        }
                    }
                    #else
                    mTableau.pivot( pivotingElement.first );
                    #endif
                    #ifdef SMTRAT_DEVOPTION_Statistics
                    mpStatistics->pivotStep();
                    #endif
                    #ifdef LRA_REFINEMENT
                    // Learn all bounds which have been deduced during the pivoting process.
                    while( !mTableau.rNewLearnedBounds().empty() )
                    {
                        PointerSet<Formula> originSet;
                        LRATableau::LearnedBound& learnedBound = mTableau.rNewLearnedBounds().back()->second;
                        mTableau.rNewLearnedBounds().pop_back();
                        vector<const LRABound*>& bounds = learnedBound.premise;
                        for( auto bound = bounds.begin(); bound != bounds.end(); ++bound )
                        {
                            assert( !(*bound)->origins().empty() );
                            originSet.insert( (*bound)->origins().begin()->begin(), (*bound)->origins().begin()->end() );
                            for( auto origin = (*bound)->origins().begin()->begin(); origin != (*bound)->origins().begin()->end(); ++origin )
                            {
                                const Constraint* constraint = (*origin)->pConstraint();
                                if( constraint != NULL )
                                {
                                    auto constrBoundIter = mTableau.rConstraintToBound().find( constraint );
                                    assert( constrBoundIter != mTableau.constraintToBound().end() );
                                    vector< const LRABound* >* constraintToBounds = constrBoundIter->second;
                                    constraintToBounds->push_back( learnedBound.nextWeakerBound );
                                    #ifdef LRA_INTRODUCE_NEW_CONSTRAINTS
                                    if( learnedBound.newBound != NULL ) constraintToBounds->push_back( learnedBound.newBound );
                                    #endif
                                }
                            }
                        }
                        activateBound( learnedBound.nextWeakerBound, originSet );
                        #ifdef LRA_INTRODUCE_NEW_CONSTRAINTS
                        if( learnedBound.newBound != NULL )
                        {
                            const Constraint* newConstraint = learnedBound.newBound->pAsConstraint();
                            addConstraintToInform( newConstraint );
                            mLinearConstraints.insert( newConstraint );
                            vector< const LRABound* >* boundVector = new vector< const LRABound* >();
                            boundVector->push_back( learnedBound.newBound );
                            mConstraintToBound[newConstraint] = boundVector;
                            activateBound( learnedBound.newBound, originSet );
                        }
                        #endif
                    }
                    #endif
                    // Maybe an easy conflict occurred with the learned bounds.
                    if( !mInfeasibleSubsets.empty() )
                    {
                        result = False;
                        goto Return;
                    }
                }
            }
            // There is a conflict, namely a basic variable violating its bounds without any suitable non-basic variable.
            else
            {
                // Create the infeasible subsets.
                #ifdef LRA_ONE_REASON
                vector< const LRABound* > conflict = mTableau.getConflict( pivotingElement.first );
                PointerSet<Formula> infSubSet;
                for( auto bound = conflict.begin(); bound != conflict.end(); ++bound )
                {
                    assert( (*bound)->isActive() );
                    infSubSet.insert( (*bound)->pOrigins()->begin()->begin(), (*bound)->pOrigins()->begin()->end() );
                }
                mInfeasibleSubsets.push_back( infSubSet );
                #else
                vector< set< const LRABound* > > conflictingBounds = mTableau.getConflictsFrom( pivotingElement.first );
                for( auto conflict = conflictingBounds.begin(); conflict != conflictingBounds.end(); ++conflict )
                {
                    PointerSet<Formula> infSubSet;
                    for( auto bound = conflict->begin(); bound != conflict->end(); ++bound )
                    {
                        assert( (*bound)->isActive() );
                        infSubSet.insert( (*bound)->pOrigins()->begin()->begin(), (*bound)->pOrigins()->begin()->end() );
                    }
                    mInfeasibleSubsets.push_back( infSubSet );
                }
                #endif
                result = False;
                goto Return;
            }
        }
        assert( false );
Return:
        #ifdef LRA_REFINEMENT
        learnRefinements();
        #endif
        #ifdef SMTRAT_DEVOPTION_Statistics
        if( result != Unknown )
        {
            mpStatistics->check( *mpReceivedFormula );
            if( result == False )
                mpStatistics->addConflict( mInfeasibleSubsets );
            mpStatistics->setNumberOfTableauxEntries( mTableau.size() );
            mpStatistics->setTableauSize( mTableau.rows().size()*mTableau.columns().size() );
        }
        #endif
        if( result != Unknown )
        {
            mTableau.resetNumberOfPivotingSteps();
            if( result == True )
            {
                // If there are unresolved notequal-constraints and the found satisfying assignment
                // conflicts this constraint, resolve it by creating the lemma (p<0 or p>0) <-> p!=0 ) and return Unknown.
                EvalRationalMap ass = getRationalModel();
                for( auto iter = mActiveUnresolvedNEQConstraints.begin(); iter != mActiveUnresolvedNEQConstraints.end(); ++iter )
                {
                    unsigned consistency = iter->first->satisfiedBy( ass );
                    assert( consistency != 2 );
                    if( consistency == 0 )
                    {
                        splitUnequalConstraint( iter->first );
                        result = Unknown;
                        break;
                    }
                }
                assert( result != True || assignmentCorrect() );
            }
        }
        #ifdef DEBUG_LRA_MODULE
        cout << endl;
        mTableau.print();
        cout << endl;
        cout << ANSWER_TO_STRING( result ) << endl;
        #endif
        return foundAnswer( result );
    }

    /**
     * Updates the current assignment into the model. Note, that this is a unique but symbolic assignment still containing delta as a variable.
     */
    void LRAModule::updateModel() const
    {
        clearModel();
        if( solverState() == True )
        {
            if( mAssignmentFullfilsNonlinearConstraints )
            {
                EvalRationalMap rationalAssignment = getRationalModel();
                for( auto ratAss = rationalAssignment.begin(); ratAss != rationalAssignment.end(); ++ratAss )
                {
                    Polynomial value = Polynomial( ratAss->second );
                    Assignment assignment = vs::SqrtEx(value);
                    mModel.insert(mModel.end(), std::make_pair(ratAss->first, assignment));
                }
            }
            else
            {
                Module::getBackendsModel();
            }
        }
    }

    /**
     * Gives a rational model if the received formula is satisfiable. Note, that it
     * is calculated from scratch every time you call this method.
     *
     * @return The rational model.
     */
    EvalRationalMap LRAModule::getRationalModel() const
    {
        if( mInfeasibleSubsets.empty() )
        {
            return mTableau.getRationalAssignment();
        }
        return EvalRationalMap();
    }

    /**
     * Returns the bounds of the variables as intervals.
     *
     * @return The bounds of the variables as intervals.
     */
    EvalIntervalMap LRAModule::getVariableBounds() const
    {
        EvalIntervalMap result = EvalIntervalMap();
        for( auto iter = mTableau.originalVars().begin(); iter != mTableau.originalVars().end(); ++iter )
        {
            const LRAVariable& var = *iter->second;
            carl::BoundType lowerBoundType;
            Rational lowerBoundValue;
            carl::BoundType upperBoundType;
            Rational upperBoundValue;
            if( var.infimum().isInfinite() )
            {
                lowerBoundType = carl::BoundType::INFTY;
                lowerBoundValue = 0;
            }
            else
            {
                lowerBoundType = var.infimum().isWeak() ? carl::BoundType::WEAK : carl::BoundType::STRICT;
                lowerBoundValue = var.infimum().limit().mainPart();
            }
            if( var.supremum().isInfinite() )
            {
                upperBoundType = carl::BoundType::INFTY;
                upperBoundValue = 0;
            }
            else
            {
                upperBoundType = var.supremum().isWeak() ? carl::BoundType::WEAK : carl::BoundType::STRICT;
                upperBoundValue = var.supremum().limit().mainPart();
            }
            Interval interval = Interval( lowerBoundValue, lowerBoundType, upperBoundValue, upperBoundType );
            result.insert( pair< carl::Variable, Interval >( iter->first, interval ) );
        }
        return result;
    }

    #ifdef LRA_REFINEMENT
    /**
     * Adds the refinements learned during pivoting to the deductions.
     */
    void LRAModule::learnRefinements()
    {
        for( auto iter = mTableau.rLearnedLowerBounds().begin(); iter != mTableau.rLearnedLowerBounds().end(); ++iter )
        {
            PointerSet<Formula> subformulas;
            for( auto bound = iter->second.premise.begin(); bound != iter->second.premise.end(); ++bound )
            {
                auto originIterB = (*bound)->origins().begin()->begin();
                while( originIterB != (*bound)->origins().begin()->end() )
                {
                    subformulas.insert( newNegation( newFormula( (*originIterB)->pConstraint() ) ) );
                    ++originIterB;
                }
            }
            subformulas.insert( newFormula( iter->second.nextWeakerBound->pAsConstraint() ) );
            addDeduction( newFormula( OR, subformulas ) );
            #ifdef SMTRAT_DEVOPTION_Statistics
            mpStatistics->addRefinement();
            mpStatistics->addDeduction();
            #endif
        }
        mTableau.rLearnedLowerBounds().clear();
        for( auto iter = mTableau.rLearnedUpperBounds().begin(); iter != mTableau.rLearnedUpperBounds().end(); ++iter )
        {
            PointerSet<Formula> subformulas;
            for( auto bound = iter->second.premise.begin(); bound != iter->second.premise.end(); ++bound )
            {
                auto originIterB = (*bound)->origins().begin()->begin();
                while( originIterB != (*bound)->origins().begin()->end() )
                {
                    subformulas.insert( newNegation( newFormula( (*originIterB)->pConstraint() ) ) );
                    ++originIterB;
                }
            }
            subformulas.insert( newFormula( iter->second.nextWeakerBound->pAsConstraint() ) );
            addDeduction( newFormula( OR, subformulas ) );
            #ifdef SMTRAT_DEVOPTION_Statistics
            mpStatistics->addRefinement();
            mpStatistics->addDeduction();
            #endif
        }
        mTableau.rLearnedUpperBounds().clear();
    }
    #endif

    /**
     * Adapt the passed formula, such that it consists of the finite infimums and supremums
     * of all variables and the non linear constraints.
     */
    void LRAModule::adaptPassedFormula()
    {
        while( !mBoundCandidatesToPass.empty() )
        {
            const LRABound& bound = *mBoundCandidatesToPass.back();
            if( bound.pInfo()->updated > 0 )
            {
                addSubformulaToPassedFormula( newFormula( bound.pAsConstraint() ), bound.origins() ); // TODO: reuse an once created formula for this constraint
                bound.pInfo()->position = --mpPassedFormula->end();
                bound.pInfo()->updated = 0;
            }
            else if( bound.pInfo()->updated < 0 )
            {
                removeSubformulaFromPassedFormula( bound.pInfo()->position );
                bound.pInfo()->position = mpPassedFormula->end();
                bound.pInfo()->updated = 0;
            }
            mBoundCandidatesToPass.pop_back();
        }
    }

    /**
     * Checks whether the current assignment of the linear constraints fulfills the non linear constraints.
     *
     * @return True, if the current assignment of the linear constraints fulfills the non linear constraints;
     *         False, otherwise.
     */
    bool LRAModule::checkAssignmentForNonlinearConstraint()
    {
        if( mNonlinearConstraints.empty() )
        {
            mAssignmentFullfilsNonlinearConstraints = true;
            return true;
        }
        else
        {
            EvalRationalMap assignments = getRationalModel();
            // Check whether the assignment satisfies the non linear constraints.
            for( auto constraint = mNonlinearConstraints.begin(); constraint != mNonlinearConstraints.end(); ++constraint )
            {
                if( (*constraint)->satisfiedBy( assignments ) != 1 )
                {
                    return false;
                }
            }
            mAssignmentFullfilsNonlinearConstraints = true;
            return true;
        }
    }

    /**
     * Activate the given bound and update the supremum, the infimum and the assignment of
     * variable to which the bound belongs.
     *
     * @param _bound The bound to activate.
     * @param _formulas The constraints which form this bound.
     */
    void LRAModule::activateBound( const LRABound* _bound, const PointerSet<Formula>& _formulas )
    {
        if( mStrongestBoundsRemoved )
        {
            mTableau.resetAssignment();
            mStrongestBoundsRemoved = false;
        }
        #ifdef LRA_SIMPLE_THEORY_PROPAGATION
        addSimpleBoundDeduction( _bound, false );
        #endif
        #ifdef LRA_SIMPLE_CONFLICT_SEARCH
        findSimpleConflicts( *_bound );
        #endif
        // If the bounds constraint has already been passed to the backend, add the given formulas to it's origins
        if( _bound->pInfo()->position != mpPassedFormula->end() )
            addOrigin( *_bound->pInfo()->position, _formulas );
        const LRAVariable& var = _bound->variable();
        const LRABound* psup = var.pSupremum();
        const LRABound& sup = *psup;
        const LRABound* pinf = var.pInfimum();
        const LRABound& inf = *pinf;
        const LRABound& bound = *_bound;
        mTableau.activateBound( _bound, _formulas );
        if( bound.isUpperBound() )
        {
            if( inf > bound.limit() && !bound.deduced() )
            {
                PointerSet<Formula> infsubset;
                infsubset.insert( bound.pOrigins()->begin()->begin(), bound.pOrigins()->begin()->end() );
                infsubset.insert( inf.pOrigins()->back().begin(), inf.pOrigins()->back().end() );
                mInfeasibleSubsets.push_back( infsubset );
            }
            if( sup > bound )
            {
                if( !sup.isInfinite() )
                    mBoundCandidatesToPass.push_back( psup );
                mBoundCandidatesToPass.push_back( _bound );
            }
        }
        if( bound.isLowerBound() )
        {
            if( sup < bound.limit() && !bound.deduced() )
            {
                PointerSet<Formula> infsubset;
                infsubset.insert( bound.pOrigins()->begin()->begin(), bound.pOrigins()->begin()->end() );
                infsubset.insert( sup.pOrigins()->back().begin(), sup.pOrigins()->back().end() );
                mInfeasibleSubsets.push_back( infsubset );
            }
            if( inf < bound )
            {
                if( !inf.isInfinite() )
                    mBoundCandidatesToPass.push_back( pinf );
                mBoundCandidatesToPass.push_back( _bound );
            }
        }
        assert( mInfeasibleSubsets.empty() || !mInfeasibleSubsets.begin()->empty() );
        #ifdef SMTRAT_DEVOPTION_Statistics
        if( !mInfeasibleSubsets.empty() )
            mpStatistics->addConflict( mInfeasibleSubsets );
        #endif
    }

    /**
     * Creates a bound corresponding to the given constraint.
     *
     * @param _var The variable to which the bound must be added.
     * @param _constraintInverted A flag, which is true if the inverted form of the given constraint forms the bound.
     * @param _boundValue The limit of the bound.
     * @param _constraint The constraint corresponding to the bound to create.
     */
    void LRAModule::setBound( const Constraint* _constraint )
    {
        pair<const LRABound*, bool> retValue = mTableau.newBound( _constraint );
        if( retValue.second )
        {
            #ifdef LRA_SIMPLE_THEORY_PROPAGATION
            addSimpleBoundDeduction( retValue.first, _constraint->relation() == Relation::NEQ );
            #endif
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            findSimpleConflicts( *retValue.first );
            #endif
        }
    }
    
    void LRAModule::addSimpleBoundDeduction( const LRABound* _bound, bool _boundNeq )
    {
        const LRAVariable& lraVar = _bound->variable();
        if( _bound->isUpperBound() )
        {
            LRABound::BoundSet::const_iterator boundPos = lraVar.upperbounds().find( _bound );
            assert( boundPos != lraVar.upperbounds().end() );
            LRABound::BoundSet::const_iterator currentBound = lraVar.upperbounds().begin();
            if( _bound->type() == LRABound::Type::EQUAL )
            {
                currentBound = boundPos;
                ++currentBound;
            }
            else
            {
                while( currentBound != boundPos )
                {
//                    if( (*currentBound)->pInfo()->exists )
//                    {
//                        PointerSet<Formula> subformulas;
//                        subformulas.insert( newNegation( newFormula( (*currentBound)->pAsConstraint() ) ) );
//                        subformulas.insert( newFormula( _boundNeq ? _bound->neqRepresentation() : _bound->pAsConstraint() ) );
//                        addDeduction( newFormula( OR, subformulas ) );
//                        #ifdef SMTRAT_DEVOPTION_Statistics
//                        mpStatistics->addDeduction();
//                        #endif
//                    }
                    ++currentBound;
                }
                ++currentBound;
            }
            if( !_boundNeq )
            {
                while( currentBound != lraVar.upperbounds().end() )
                {
                    if( (*currentBound)->pInfo()->exists && (*currentBound)->type() != LRABound::Type::EQUAL )
                    {
                        PointerSet<Formula> subformulas;
                        subformulas.insert( newNegation( newFormula( _bound->pAsConstraint() ) ) );
                        subformulas.insert( newFormula( (*currentBound)->pAsConstraint() ) );
                        addDeduction( newFormula( OR, subformulas ) );
                        #ifdef SMTRAT_DEVOPTION_Statistics
                        mpStatistics->addDeduction();
                        #endif
                    }
                    ++currentBound;
                }
            }
        }
        if( _bound->isLowerBound() )
        {
            LRABound::BoundSet::const_iterator boundPos = lraVar.lowerbounds().find( _bound );
            assert( boundPos != lraVar.lowerbounds().end() );
            LRABound::BoundSet::const_iterator currentBound = lraVar.lowerbounds().begin();
            if( _boundNeq )
            {
                currentBound = boundPos;
                ++currentBound;
            }
            else
            {
                while( currentBound != boundPos )
                {
                    if( (*currentBound)->pInfo()->exists && (*currentBound)->type() != LRABound::Type::EQUAL )
                    {
                        PointerSet<Formula> subformulas;
                        subformulas.insert( newNegation( newFormula( _bound->pAsConstraint() ) ) );
                        subformulas.insert( newFormula( (*currentBound)->pAsConstraint() ) );
                        addDeduction( newFormula( OR, subformulas ) );
                        #ifdef SMTRAT_DEVOPTION_Statistics
                        mpStatistics->addDeduction();
                        #endif
                    }
                    ++currentBound;
                }
//                ++currentBound;
            }
//            if( _bound->type() != LRABound::Type::EQUAL )
//            {
//                while( currentBound != lraVar.lowerbounds().end() )
//                {
//                    if( (*currentBound)->pInfo()->exists )
//                    {
//                        PointerSet<Formula> subformulas;
//                        subformulas.insert( newNegation( newFormula( (*currentBound)->pAsConstraint() ) ) );
//                        subformulas.insert( newFormula( _boundNeq ? _bound->neqRepresentation() : _bound->pAsConstraint() ) );
//                        addDeduction( newFormula( OR, subformulas ) );
//                        #ifdef SMTRAT_DEVOPTION_Statistics
//                        mpStatistics->addDeduction();
//                        #endif
//                    }
//                    ++currentBound;
//                }
//            }
        }
    }
    
    /**
     * 
     * @param _premise
     * @param _conclusion
     * @param _conlusionNeq
     */
    void LRAModule::addSimpleBoundConflict( const LRABound& _caseA, const LRABound& _caseB, bool _caseBneq )
    {
        PointerSet<Formula> subformulas;
        subformulas.insert( newNegation( newFormula( _caseA.pAsConstraint() ) ) );
        subformulas.insert( newNegation( newFormula( _caseBneq ? _caseB.neqRepresentation() : _caseB.pAsConstraint() ) ) );
        addDeduction( newFormula( OR, subformulas ) );
        #ifdef SMTRAT_DEVOPTION_Statistics
        mpStatistics->addDeduction();
        #endif
    }

    /**
     * Finds all conflicts between lower resp. upper bounds and the given upper
     * resp. lower bound and adds them to the deductions.
     *
     * @param _bound The bound to find conflicts for.
     */
    void LRAModule::findSimpleConflicts( const LRABound& _bound )
    {
        assert( !_bound.deduced() );
        if( _bound.isUpperBound() )
        {
            const LRABound::BoundSet& lbounds = _bound.variable().lowerbounds();
            for( auto lbound = lbounds.rbegin(); lbound != --lbounds.rend(); ++lbound )
            {
                if( **lbound > _bound.limit() && (*lbound)->pAsConstraint() != NULL )
                {
                    if( (*lbound)->neqRepresentation() != NULL )
                    {
                        if( _bound.type() == LRABound::EQUAL && (*lbound)->limit().mainPart() == _bound.limit().mainPart() )
                        {
                            addSimpleBoundConflict( _bound, **lbound, true );
                        }
                    }
                    else if( _bound.neqRepresentation() != NULL )
                    {
                        if( (*lbound)->type() == LRABound::EQUAL && (*lbound)->limit().mainPart() == _bound.limit().mainPart() )
                        {
                            addSimpleBoundConflict( **lbound, _bound, true );
                        }
                    }
                    else
                    {
                        addSimpleBoundConflict( _bound, **lbound );
                    }
                }
                else
                {
                    break;
                }
            }
        }
        if( _bound.isLowerBound() )
        {
            const LRABound::BoundSet& ubounds = _bound.variable().upperbounds();
            for( auto ubound = ubounds.begin(); ubound != --ubounds.end(); ++ubound )
            {
                if( **ubound < _bound.limit() && (*ubound)->pAsConstraint() != NULL )
                {
                    if( (*ubound)->neqRepresentation() != NULL )
                    {
                        if( _bound.type() == LRABound::EQUAL && (*ubound)->limit().mainPart() == _bound.limit().mainPart() )
                        {
                            addSimpleBoundConflict( _bound, **ubound, true );
                        }
                    }
                    else if( _bound.neqRepresentation() != NULL )
                    {
                        if( (*ubound)->type() == LRABound::EQUAL && (*ubound)->limit().mainPart() == _bound.limit().mainPart() )
                        {
                            addSimpleBoundConflict( **ubound, _bound, true );
                        }
                    }
                    else
                    {
                        addSimpleBoundConflict( _bound, **ubound );
                    }
                }
                else
                {
                    break;
                }
            }
        }
    }

    /**
     * Initializes the tableau according to all linear constraints, of which this module has been informed.
     */
    void LRAModule::init()
    {
        if( !mInitialized )
        {
            mInitialized = true;
//            map<carl::Variable, PointerSet<Constraint>> linearConstraintSCCs;
//            for( const Constraint* constraint : mLinearConstraints )
//            {
//                const Variables& vars = constraint->variables();
//                for( carl::Variable var : vars )
//                {
//                    linearConstraintSCCs[var].insert( constraint );
//                }
//            }
            for( const Constraint* constraint : mLinearConstraints )
            {
                setBound( constraint );
            }
//            mTableau.setSize( mTableau.slackVars().size(), mTableau.originalVars().size(), mLinearConstraints.size() );
            #ifdef LRA_USE_PIVOTING_STRATEGY
            mTableau.setBlandsRuleStart( 1000 );//(unsigned) mTableau.columns().size() );
            #endif
        }
    }
    
    /**
     * 
     * @return True, if a branching occurred.
     *         False, otherwise.
     */
    bool LRAModule::gomory_cut()
    {
        EvalRationalMap rMap_ = getRationalModel();
        bool all_int = true;
        for( LRAVariable* basicVar : mTableau.rows() )
        {            
            if( basicVar->isOriginal() )
            {
                Variables vars;
                basicVar->expression().gatherVariables( vars );
                assert( vars.size() == 1 );
                auto found_ex = rMap_.find(*vars.begin()); 
                Rational& ass = found_ex->second;
                if( !carl::isInteger( ass ) )
                {
                    all_int = false;
                    const Constraint* gomory_constr = mTableau.gomoryCut(ass, basicVar);
                    if( gomory_constr != NULL )
                    { 
                        assert( !gomory_constr->satisfiedBy( rMap_ ) );
                        PointerSet<Formula> subformulas; 
                        mTableau.collect_premises( basicVar, subformulas );
                        PointerSet<Formula> premise;
                        for( const Formula* pre : subformulas )
                        {
                            premise.insert( newNegation( pre ) );
                        }
                        const Formula* gomory_formula = newFormula( gomory_constr );
                        premise.insert( gomory_formula );
                        addDeduction( newFormula( OR, std::move( premise ) ) );
                    } 
                }
            }    
        }          
        return !all_int;
    }
    
    #ifdef LRA_CUTS_FROM_PROOFS
    /**
     * @return true, if a branching occurred.
     *         false, otherwise.
     */
    bool LRAModule::cuts_from_proofs()
    {
        #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
        cout << "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~" << endl;
        cout << "Cut from proofs:" << endl;
        mTableau.print();
        #endif
        // Check if the solution is integer.
        EvalRationalMap _rMap = getRationalModel();
        auto map_iterator = _rMap.begin();
        auto var = mTableau.originalVars().begin();
        while( var != mTableau.originalVars().end() )
        {
            assert( var->first == map_iterator->first );
            Rational& ass = map_iterator->second; 
            if( var->first.getType() == carl::VariableType::VT_INT && !carl::isInteger( ass ) )
            {
                #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
                cout << "Fix: " << var->first << endl;
                #endif
                break;
            }
            ++map_iterator;
            ++var;
        }
        if( var == mTableau.originalVars().end() )
        {
            #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
            cout << "Assignment is already integer!" << endl;
            cout << "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~" << endl;
            #endif
            return false;
        }
        /*
         * Build the new Tableau consisting out of the defining constraints.
         */
        LRATableau dc_Tableau = LRATableau( mpPassedFormula->end() );  
        size_t numRows = mTableau.rows().size();
        size_t dc_count = 0;
        LRAEntryType max_value = 0;
        vector<size_t> dc_positions = vector<size_t>();
        std::vector< const Constraint* > DC_Matrix = std::vector< const Constraint* >();
        for( size_t i = 0; i < numRows; ++i )
        {
            LRAEntryType lcmOfCoeffDenoms = 1;
            const Constraint* dc_constraint = mTableau.isDefining( i, max_value );
            if( dc_constraint != NULL  )
            {
                size_t row_count_before = dc_Tableau.rows().size();
                pair< const LRABound*, bool> result = dc_Tableau.newBound(dc_constraint);
                PointerSet<Formula> formulas;
                dc_Tableau.activateBound(result.first, formulas);
                if( row_count_before < dc_Tableau.rows().size() )
                {
                    dc_count++;
                    dc_positions.push_back(i);  
                    DC_Matrix.push_back( dc_constraint );
                }
            }   
        }
        auto pos = mProcessedDCMatrices.find( DC_Matrix );
        if( pos == mProcessedDCMatrices.end() )
        {
            mProcessedDCMatrices.insert( DC_Matrix );
        }
        if( dc_Tableau.rows().size() > 0 && pos == mProcessedDCMatrices.end() )
        {
            #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
            cout << "Defining constraints:" << endl;
            dc_Tableau.print();   
            #endif

            // At least one DC exists -> Construct and embed it.
            vector<size_t> diagonals = vector<size_t>();    
            vector<size_t>& diagonals_ref = diagonals;               
            /*
            dc_Tableau.addColumns(0,2,2);
            dc_Tableau.addColumns(1,2,4);
            dc_Tableau.addColumns(2,2,2);
            dc_Tableau.addColumns(3,4,1);
            dc_Tableau.addColumns(5,4,1);
            dc_Tableau.addColumns(4,4,-1);
            dc_Tableau.print( LAST_ENTRY_ID, std::cout, "", true, true );
            */
            bool full_rank = true;
            dc_Tableau.calculate_hermite_normalform( diagonals_ref, full_rank );
            if( !full_rank )
            {
                branchAt( Polynomial( var->first ), (Rational)map_iterator->second );
                return true;
            }
            #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
            cout << "HNF of defining constraints:" << endl;
            dc_Tableau.print( LAST_ENTRY_ID, std::cout, "", true, true );
            cout << "Actual order of columns:" << endl;
            for( auto iter = diagonals.begin(); iter != diagonals.end(); ++iter ) 
                printf( "%u", *iter );
            #endif  
            dc_Tableau.invert_HNF_Matrix( diagonals );
            #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
            cout << "Inverted matrix:" << endl;
            dc_Tableau.print( LAST_ENTRY_ID, std::cout, "", true, true );
            #endif 
            Polynomial* cut_from_proof = new Polynomial();
            for( size_t i = 0; i < dc_positions.size(); ++i )
            {
                LRAEntryType upper_lower_bound;
                cout << "Premise for CFP is fulfilled!" << endl;
                cut_from_proof = dc_Tableau.create_cut_from_proof( dc_Tableau, mTableau, i, diagonals, dc_positions, upper_lower_bound, max_value );
                if( cut_from_proof != NULL )
                {
                    #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
                    cout << "Proof of unsatisfiability:  " << *cut_from_proof << " = 0" << endl;
                    #endif
                    if( mTableau.slackVars().size() > 1 ) exit(7771);
                    LRAEntryType bound_add = 1;
                    LRAEntryType bound = upper_lower_bound;
                    if( carl::isInteger( upper_lower_bound ) )
                    {
                        bound_add = 0;
                    }
                    const smtrat::Constraint* cut_constraint = newConstraint( *cut_from_proof - (Rational)carl::floor((Rational)upper_lower_bound) , Relation::LEQ );
                    const smtrat::Constraint* cut_constraint2 = newConstraint( *cut_from_proof - ((Rational)carl::floor((Rational)upper_lower_bound)+bound_add) , Relation::GEQ );
                    // Construct and add (p<=I-1 or p>=I))
                    const Formula* cons1 = newFormula( cut_constraint );
                    cons1->setActivity( -numeric_limits<double>::infinity() );
                    const Formula* cons2 = newFormula( cut_constraint2 );
                    cons2->setActivity( -numeric_limits<double>::infinity() );
                    PointerSet<Formula> subformulasA;
                    subformulasA.insert( cons1 );
                    subformulasA.insert( cons2 );
                    addDeduction( newFormula( OR, std::move( subformulasA ) ) );   
                    // (not(p<=I-1) or not(p>=I))
                    PointerSet<Formula> subformulasB;
                    subformulasB.insert( newNegation( cons1 ) );
                    subformulasB.insert( newNegation( cons2 ) );
                    addDeduction( newFormula( OR, std::move( subformulasB ) ) );
                    #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
                    cout << "After adding proof of unsatisfiability:" << endl;
                    mTableau.print( LAST_ENTRY_ID, std::cout, "", true, true );
                    cout << "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~" << endl;
                    #endif
                    return true;
                }
                else 
                    cout << "No CFP found!" << endl;
            }
            #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
            cout << "Found no proof of unsatisfiability!" << endl;
            #endif
        }
        #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
            cout << "No defining constraint!" << endl;
        cout << "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~" << endl;
        cout << "Branch at: " << var->first << endl;
        #endif
        branchAt( Polynomial( var->first ), (Rational)map_iterator->second );
        return true;
    }
    #endif

    enum BRANCH_STRATEGY
    {
        MIN_PIVOT,
        MOST_FEASIBLE,
        MOST_INFEASIBLE,
        NATIVE
    };
    
    /**
     * @return true, if a branching occurred.
     *         false, otherwise.
     */
    bool LRAModule::branch_and_bound()
    {
        BRANCH_STRATEGY strat = MOST_INFEASIBLE;
        bool gc_support = true;
        bool result = true;
        if( strat == MIN_PIVOT )
        {
            result = minimal_row_var( gc_support );            
        }
        else if( strat == MOST_FEASIBLE )
        {
            result = most_feasible_var( gc_support );
        }
        else if( strat == MOST_INFEASIBLE )
        {
            result = most_infeasible_var( gc_support );
        }
        else if( strat == NATIVE )
        {
            result = first_var( gc_support );
        }  
        return result;
    }
    
    bool LRAModule::maybeGomoryCut( const LRAVariable* _lraVar, const Rational& _branchingValue )
    {
        if( probablyLooping( _lraVar->expression(), _branchingValue ) )
        {
            return gomory_cut();
//            if( gomory_cut() )
//            {
//                mProbableLoopCounter = 0;
//            }
//            else
//            {
//                if( mProbableLoopCounter < 3 )
//                {
//                    ++mProbableLoopCounter;
//                }
//                else 
//                    return false;
//            }
        }
        //PointerSet<Formula> premises;
        //mTableau.collect_premises( _lraVar , premises  );  
        branchAt( _lraVar->expression(), _branchingValue );
        return true;
    }
    
     /**
      * @return true,  if a branching occured with an original variable that has to be fixed 
      *                which has the lowest count of entries in its row.
      *         false, if no branching occured.
      */    
    bool LRAModule::minimal_row_var( bool& gc_support )
    {
        EvalRationalMap _rMap = getRationalModel();
        auto map_iterator = _rMap.begin();
        auto branch_var = mTableau.originalVars().begin();
        Rational ass_;
        Rational row_count_min = mTableau.columns().size()+1;
        bool result = false;
        for( auto var = mTableau.originalVars().begin(); var != mTableau.originalVars().end(); ++var )
        {
            assert( var->first == map_iterator->first );
            Rational& ass = map_iterator->second; 
            if( var->first.getType() == carl::VariableType::VT_INT && !carl::isInteger( ass ) )
            {
                size_t row_count_new = mTableau.getNumberOfEntries( var->second );
                if( row_count_new < row_count_min )
                {
                    result = true;
                    row_count_min = row_count_new; 
                    branch_var = var;
                    ass_ = ass; 
                }
            }
            ++map_iterator;
        }
        if( result )
        {
            if( gc_support )
            {
                return maybeGomoryCut( branch_var->second, ass_ );
            }
            //PointerSet<Formula> premises;
            //mTableau.collect_premises( branch_var->second , premises  );                
            branchAt( branch_var->second->expression(), ass_ );
            return true;
        }
        else
        {
            return false;
        }
    }
    
     /**
      * @return true,  if a branching occured with an original variable that has to be fixed 
      *                which is most feasible.
      *         false, if no branching occured.
      */    
    bool LRAModule::most_feasible_var( bool& gc_support )
    {
        EvalRationalMap _rMap = getRationalModel();
        auto map_iterator = _rMap.begin();
        auto branch_var = mTableau.originalVars().begin();
        Rational ass_;
        bool result = false;
        Rational diff = -1;
        for( auto var = mTableau.originalVars().begin(); var != mTableau.originalVars().end(); ++var )
        {
            assert( var->first == map_iterator->first );
            Rational& ass = map_iterator->second; 
            if( var->first.getType() == carl::VariableType::VT_INT && !carl::isInteger( ass ) )
            {
                Rational curr_diff = ass - carl::floor(ass);
                if( carl::abs( curr_diff -  (Rational)1/2 ) > diff )
                {
                    result = true;
                    diff = carl::abs( curr_diff -  (Rational)1/2 ); 
                    branch_var = var;
                    ass_ = ass;                   
                }
            }
            ++map_iterator;
        }
        if( result )
        {
            if( gc_support )
            {
                return maybeGomoryCut( branch_var->second, ass_ );
            }
            //PointerSet<Formula> premises;
            //mTableau.collect_premises( branch_var->second , premises  );                
            branchAt( branch_var->second->expression(), ass_ );
            return true;         
        }
        else
        {
            return false;
        } 
    }
    
     /**
      * @return true,  if a branching occured with an original variable that has to be fixed 
      *                which is most infeasible.
      *         false, if no branching occured.
      */   
    bool LRAModule::most_infeasible_var( bool& gc_support ) 
    {
        EvalRationalMap _rMap = getRationalModel();
        auto map_iterator = _rMap.begin();
        auto branch_var = mTableau.originalVars().begin();
        Rational ass_;
        bool result = false;
        Rational diff = 1;
        for( auto var = mTableau.originalVars().begin(); var != mTableau.originalVars().end(); ++var )
        {
            assert( var->first == map_iterator->first );
            Rational& ass = map_iterator->second; 
            if( var->first.getType() == carl::VariableType::VT_INT && !carl::isInteger( ass ) )
            {
                Rational curr_diff = ass - carl::floor(ass);
                if( carl::abs( curr_diff -  (Rational)1/2 ) < diff )
                {
                    result = true;
                    diff = carl::abs( curr_diff -  (Rational)1/2 ); 
                    branch_var = var;
                    ass_ = ass;                   
                }
            }
            ++map_iterator;
        }
        if( result )
        {
            if( gc_support )
            {
                return maybeGomoryCut( branch_var->second, ass_ );
            }
            //PointerSet<Formula> premises;
            //mTableau.collect_premises( branch_var->second , premises  ); 
            branchAt( branch_var->second->expression(), ass_ );
            return true;
        }
        else
        {
            return false;
        } 
    }
    
     /**
      * @return true,  if a branching occured with the first original variable that has to be fixed.
      *         false, if no branching occured.
      */    
    bool LRAModule::first_var( bool& gc_support )
    {
        EvalRationalMap _rMap = getRationalModel();
        auto map_iterator = _rMap.begin();
        for( auto var = mTableau.originalVars().begin(); var != mTableau.originalVars().end(); ++var )
        {
            assert( var->first == map_iterator->first );
            Rational& ass = map_iterator->second; 
            if( var->first.getType() == carl::VariableType::VT_INT && !carl::isInteger( ass ) )
            {
                if( gc_support )
                {
                    return maybeGomoryCut( var->second, ass );
                }
                //PointerSet<Formula> premises;
                //mTableau.collect_premises( var->second, premises  ); 
                branchAt( var->second->expression(), ass );
                return true;           
            }
            ++map_iterator;
        } 
        return false;
    }
    
    /**
     * Checks whether the found assignment is consistent with the tableau, hence replacing the original
     * variables in the expressions represented by the slack variables equals their assignment.
     * @param _assignment The assignment of the original variables.
     * @param _delta The calculated delta for the given assignment.
     * @return true, if the found assignment is consistent with the tableau;
     *         false, otherwise.
     */
    bool LRAModule::assignmentConsistentWithTableau( const EvalRationalMap& _assignment, const LRABoundType& _delta ) const
    {
        for( auto slackVar : mTableau.slackVars() )
        {
            Polynomial tmp = slackVar.first->substitute( _assignment );
            assert( tmp.isConstant() );
            LRABoundType slackVarAssignment = slackVar.second->assignment().mainPart() + slackVar.second->assignment().deltaPart() * _delta;
            if( !(tmp == (Rational) slackVarAssignment) )
            {
                return false;
            }
        }
        return true;
    }
    
    /**
     * @return true, if the encountered satisfying assignment for the received formula
     *               indeed satisfies it;
     *         false, otherwise.
     */
    bool LRAModule::assignmentCorrect() const
    {
        if( solverState() == False ) return true;
        EvalRationalMap model = getRationalModel();
        for( auto ass = model.begin(); ass != model.end(); ++ass )
        {
            if( ass->first.getType() == carl::VariableType::VT_INT && !carl::isInteger( ass->second ) )
            {
                return false;
            }
        }
        for( auto constraint = mpReceivedFormula->begin(); constraint != mpReceivedFormula->end(); ++constraint )
        {
            if( (*constraint)->constraint().satisfiedBy( model ) != 1 )
            {
                assert( (*constraint)->constraint().satisfiedBy( model ) == 0 );
                return false;
            }
        }
        return true;
    }

    /**
     * Prints all linear constraints.
     *
     * @param _out The output stream to print on.
     * @param _init The beginning of each line to print.
     */
    void LRAModule::printLinearConstraints( ostream& _out, const string _init ) const
    {
        _out << _init << "Linear constraints:" << endl;
        for( auto iter = mLinearConstraints.begin(); iter != mLinearConstraints.end(); ++iter )
        {
            _out << _init << "   " << (*iter)->toString() << endl;
        }
    }

    /**
     * Prints all non-linear constraints.
     *
     * @param _out The output stream to print on.
     * @param _init The beginning of each line to print.
     */
    void LRAModule::printNonlinearConstraints( ostream& _out, const string _init ) const
    {
        _out << _init << "Nonlinear constraints:" << endl;
        for( auto iter = mNonlinearConstraints.begin(); iter != mNonlinearConstraints.end(); ++iter )
        {
            _out << _init << "   " << (*iter)->toString() << endl;
        }
    }

    /**
     * Prints the mapping of constraints to their corresponding bounds.
     *
     * @param _out The output stream to print on.
     * @param _init The beginning of each line to print.
     */
    void LRAModule::printConstraintToBound( ostream& _out, const string _init ) const
    {
        _out << _init << "Mapping of constraints to bounds:" << endl;
        for( auto iter = mTableau.constraintToBound().begin(); iter != mTableau.constraintToBound().end(); ++iter )
        {
            _out << _init << "   " << iter->first->toString() << endl;
            for( auto iter2 = iter->second->begin(); iter2 != iter->second->end(); ++iter2 )
            {
                _out << _init << "        ";
                (*iter2)->print( true, cout, true );
                _out << endl;
            }
        }
    }

    /**
     * Prints the strictest bounds, which have to be passed the backend in case.
     *
     * @param _out The output stream to print on.
     * @param _init The beginning of each line to print.
     */
    void LRAModule::printBoundCandidatesToPass( ostream& _out, const string _init ) const
    {
        _out << _init << "Bound candidates to pass:" << endl;
        for( auto iter = mBoundCandidatesToPass.begin(); iter != mBoundCandidatesToPass.end(); ++iter )
        {
            _out << _init << "   ";
            (*iter)->print( true, cout, true );
            _out << " [" << (*iter)->pInfo()->updated << "]" << endl;
        }
    }

    /**
     * Prints the current rational assignment.
     *
     * @param _out The output stream to print on.
     * @param _init The beginning of each line to print.
     */
    void LRAModule::printRationalModel( ostream& _out, const string _init ) const
    {
        EvalRationalMap rmodel = getRationalModel();
        _out << _init << "Rational model:" << endl;
        for( auto assign = rmodel.begin(); assign != rmodel.end(); ++assign )
        {
            _out << _init;
            _out << setw(10) << assign->first;
            _out << " -> " << assign->second << endl;
        }
    }

    /**
     * Prints the current tableau.
     *
     * @param _out The output stream to print on.
     * @param _init The beginning of each line to print.
     */
    void LRAModule::printTableau( ostream& _out, const string _init ) const
    {
        mTableau.print( LAST_ENTRY_ID, _out, _init );
    }

    /**
     * Prints all lra variables and their assignments.
     *
     * @param _out The output stream to print on.
     * @param _init The beginning of each line to print.
     */
    void LRAModule::printVariables( ostream& _out, const string _init ) const
    {
        mTableau.printVariables( true, _out, _init );
    }
}    // namespace smtrat

