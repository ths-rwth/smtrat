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
#ifndef LRA_GOMORY_CUTS
#ifndef LRA_CUTS_FROM_PROOFS
#define LRA_BRANCH_AND_BOUND
#endif
#endif

using namespace std;
using namespace smtrat::lra;

namespace smtrat
{
    LRAModule::LRAModule( ModuleType _type, const Formula* const _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* const _manager ):
        Module( _type, _formula, _conditionals, _manager ),
        mInitialized( false ),
        mAssignmentFullfilsNonlinearConstraints( false ),
        mTableau( mpPassedFormula->end() ),
        mLinearConstraints(),
        mNonlinearConstraints(),
        mActiveResolvedNEQConstraints(),
        mActiveUnresolvedNEQConstraints(),
        mResolvedNEQConstraints(),
        mDelta( Formula::newAuxiliaryRealVariable( "delta_" + to_string( id() ) ) ),
        mBoundCandidatesToPass()
    {
        #ifdef SMTRAT_DEVOPTION_Statistics
        stringstream s;
        s << moduleName( type() ) << "_" << id();
        mpStatistics = new LRAModuleStatistics( s.str() );
        #endif
    }

    LRAModule::~LRAModule()
    {}

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
        cout << "inform about " << *_constraint << endl;
        #endif
        Module::inform( _constraint );
        if( !_constraint->lhs().isConstant() && _constraint->lhs().isLinear() )
        {
            bool elementInserted = mLinearConstraints.insert( _constraint ).second;
            if( elementInserted && mInitialized )
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
    bool LRAModule::assertSubformula( Formula::const_iterator _subformula )
    {
        #ifdef DEBUG_LRA_MODULE
        cout << "add " << **_subformula << "(" << *_subformula << ")" << endl;
        #endif
        Module::assertSubformula( _subformula );
        switch( (*_subformula)->getType() )
        {
            case FFALSE:
            {
                set< const Formula* > infSubSet = set< const Formula* >();
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
                if( !mInitialized ) init();
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
                        if( (*_subformula)->constraint().relation() != Relation::NEQ )
                        {
                            auto constrBoundIter = mTableau.constraintToBound().find( constraint );
                            assert( constrBoundIter != mTableau.constraintToBound().end() );
                            const vector< const LRABound* >* bounds = constrBoundIter->second;
                            assert( bounds != NULL );

                            set<const Formula*> originSet = set<const Formula*>();
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
                            assert( mInfeasibleSubsets.empty() || !mInfeasibleSubsets.begin()->empty() );
                            #ifdef SMTRAT_DEVOPTION_Statistics
                            if( !mInfeasibleSubsets.empty() && mNonlinearConstraints.empty() )
                                mpStatistics->addConflict( mInfeasibleSubsets );
                            #endif
                            return mInfeasibleSubsets.empty() || !mNonlinearConstraints.empty(); // TODO: If there is an infeasible subset we should always return false, shouldn't we?
                        }
                        else
                        {
                            auto constrBoundIter = mTableau.constraintToBound().find( constraint );
                            assert( constrBoundIter != mTableau.constraintToBound().end() );
                            const vector< const LRABound* >* bounds = constrBoundIter->second;
                            assert( bounds != NULL );
                            assert( bounds->size() == 2 );
                            if( (*bounds)[0]->isActive() || (*bounds)[1]->isActive() )
                            {
                                Context context = Context();
                                context.origin = *_subformula;
                                context.position = mpPassedFormula->end();
                                mActiveResolvedNEQConstraints.insert( pair< const Constraint*, Context >( constraint, context ) );
                            }
                            else
                            {
                                addSubformulaToPassedFormula( new Formula( constraint ), *_subformula );
                                Context context = Context();
                                context.origin = *_subformula;
                                context.position = mpPassedFormula->last();
                                mActiveUnresolvedNEQConstraints.insert( pair< const Constraint*, Context >( constraint, context ) );
                            }
                        }
                    }
                    else
                    {
                        addSubformulaToPassedFormula( new Formula( constraint ), *_subformula );
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
    void LRAModule::removeSubformula( Formula::const_iterator _subformula )
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
                    if( (*_subformula)->constraint().relation() != Relation::NEQ )
                    {
                        // Deactivate the bounds regarding the given constraint
                        auto constrBoundIter = mTableau.constraintToBound().find( constraint );
                        assert( constrBoundIter != mTableau.rConstraintToBound().end() );
                        vector< const LRABound* >* bounds = constrBoundIter->second;
                        assert( bounds != NULL );
                        auto bound = bounds->begin();
                        while( bound != bounds->end() )
                        {
                            if( !(*bound)->origins().empty() )
                            {
                                auto originSet = (*bound)->pOrigins()->begin();
                                while( originSet != (*bound)->origins().end() )
                                {
                                    if( originSet->find( *_subformula ) != originSet->end() )
                                    {
                                        originSet = (*bound)->pOrigins()->erase( originSet );
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
                                        assert( uebounds->size() == 2 );
                                        if( !(*uebounds)[0]->isActive() && !(*uebounds)[1]->isActive() )
                                        {
                                            auto pos = mActiveResolvedNEQConstraints.find( (*bound)->neqRepresentation() );
                                            if( pos != mActiveResolvedNEQConstraints.end() )
                                            {
                                                auto entry = mActiveUnresolvedNEQConstraints.insert( *pos );
                                                mActiveResolvedNEQConstraints.erase( pos );
                                                addSubformulaToPassedFormula( new Formula( entry.first->first ), entry.first->second.origin );
                                                entry.first->second.position = mpPassedFormula->last();
                                            }
                                        }
                                    }
                                    LRAVariable& var = *(*bound)->pVariable();
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
                            if( bound != bounds->begin() && (*bound)->origins().empty() )
                                bound = bounds->erase( bound );
                            else
                                ++bound;
                        }
                    }
                    else
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
        // If there are unresolved notequal-constraints, resolve the notequal-constraints 
        // (create the lemma (p<0 or p>0) <-> p!=0 ) and return Unknown.
        if( !mActiveUnresolvedNEQConstraints.empty() )
        {
            for( auto iter = mActiveUnresolvedNEQConstraints.begin(); iter != mActiveUnresolvedNEQConstraints.end(); ++iter )
            {
                if( mResolvedNEQConstraints.find( iter->first ) == mResolvedNEQConstraints.end() )
                {
                    splitUnequalConstraint( iter->first );
                    mResolvedNEQConstraints.insert( iter->first );
                }
            }
            goto Return; // Unknown
        }
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
                    assert( mActiveUnresolvedNEQConstraints.empty() );
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
                        #ifdef LRA_BRANCH_AND_BOUND
                        if( branch_and_bound() )
                            goto Return; // Unknown
                        #endif
                        result = True;
//                        if( !assignmentCorrect() )
//                            exit( 7771 );
                        assert( assignmentCorrect() );
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
                    mTableau.pivot( pivotingElement.first );
                    #ifdef SMTRAT_DEVOPTION_Statistics
                    mpStatistics->pivotStep();
                    #endif
                    #ifdef LRA_REFINEMENT
                    // Learn all bounds which have been deduced during the pivoting process.
                    while( !mTableau.rNewLearnedBounds().empty() )
                    {
                        set< const Formula*> originSet = set< const Formula*>();
                        LRATableau::LearnedBound& learnedBound = mTableau.rNewLearnedBounds().back()->second;
                        mTableau.rNewLearnedBounds().pop_back();
                        vector<const LRABound*>& bounds = *learnedBound.premise;
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
                set< const Formula* > infSubSet;
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
                    set< const Formula* > infSubSet;
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
        EvalRationalMap result = EvalRationalMap();
        if( mInfeasibleSubsets.empty() )
        {
            LRABoundType minDelta = -1;
            LRABoundType curDelta = 0;
            LRAVariable* variable = NULL;
            // For all slack variables find the minimum of all (c2-c1)/(k1-k2), where ..
            for( auto originalVar = mTableau.originalVars().begin(); originalVar != mTableau.originalVars().end(); ++originalVar )
            {
                variable = originalVar->second;
                const LRAValue& assValue = variable->assignment();
                const LRABound& inf = variable->infimum();
                if( !inf.isInfinite() )
                {
                    // .. the supremum is c2+k2*delta, the variable assignment is c1+k1*delta, c1<c2 and k1>k2.
                    if( inf.limit().mainPart() < assValue.mainPart() && inf.limit().deltaPart() > assValue.deltaPart() )
                    {
                        curDelta = ( assValue.mainPart() - inf.limit().mainPart() ) / ( inf.limit().deltaPart() - assValue.deltaPart() );
                        if( minDelta < 0 || curDelta < minDelta )
                            minDelta = curDelta;
                    }
                }
                const LRABound& sup = variable->supremum();
                if( !sup.isInfinite() )
                {
                    // .. the infimum is c1+k1*delta, the variable assignment is c2+k2*delta, c1<c2 and k1>k2.
                    if( sup.limit().mainPart() > assValue.mainPart() && sup.limit().deltaPart() < assValue.deltaPart() )
                    {
                        curDelta = ( sup.limit().mainPart() - assValue.mainPart() ) / ( assValue.deltaPart() - sup.limit().deltaPart() );
                        if( minDelta < 0 || curDelta < minDelta )
                            minDelta = curDelta;
                    }
                }
            }
            // For all slack variables find the minimum of all (c2-c1)/(k1-k2), where ..
            for( auto slackVar = mTableau.slackVars().begin(); slackVar != mTableau.slackVars().end(); ++slackVar )
            {
                variable = slackVar->second;
                if( !variable->isActive() ) continue;
                const LRAValue& assValue = variable->assignment();
                const LRABound& inf = variable->infimum();
                if( !inf.isInfinite() )
                {
                    // .. the infimum is c1+k1*delta, the variable assignment is c2+k2*delta, c1<c2 and k1>k2.
                    if( inf.limit().mainPart() < assValue.mainPart() && inf.limit().deltaPart() > assValue.deltaPart() )
                    {
                        curDelta = ( assValue.mainPart() - inf.limit().mainPart() ) / ( inf.limit().deltaPart() - assValue.deltaPart() );
                        if( minDelta < 0 || curDelta < minDelta )
                            minDelta = curDelta;
                    }
                }
                const LRABound& sup = variable->supremum();
                if( !sup.isInfinite() )
                {
                    // .. the supremum is c2+k2*delta, the variable assignment is c1+k1*delta, c1<c2 and k1>k2.
                    if( sup.limit().mainPart() > assValue.mainPart() && sup.limit().deltaPart() < assValue.deltaPart() )
                    {
                        curDelta = ( sup.limit().mainPart() - assValue.mainPart() ) / ( assValue.deltaPart() - sup.limit().deltaPart() );
                        if( minDelta < 0 || curDelta < minDelta )
                            minDelta = curDelta;
                    }
                }
            }

            curDelta = minDelta < 0 ? 1 : minDelta;
            // Calculate the rational assignment of all original variables.
            for( auto var = mTableau.originalVars().begin(); var != mTableau.originalVars().end(); ++var )
            {
                LRABoundType value = var->second->assignment().mainPart() + var->second->assignment().deltaPart() * curDelta;
                result.insert( pair< const carl::Variable, Rational >( var->first, value ) );
            }
//            assert( assignmentConsistentWithTableau( result, curDelta ) );
        }
        return result;
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
        map<LRAVariable*, typename LRATableau::LearnedBound>& llBs = mTableau.rLearnedLowerBounds();
        while( !llBs.empty() )
        {
            Formula* deduction = new Formula( OR );
            for( auto bound = llBs.begin()->second.premise->begin(); bound != llBs.begin()->second.premise->end(); ++bound )
            {
                auto originIterB = (*bound)->origins().begin()->begin();
                while( originIterB != (*bound)->origins().begin()->end() )
                {
                    deduction->addSubformula( new Formula( NOT ) );
                    deduction->back()->addSubformula( (*originIterB)->pConstraint() );
                    ++originIterB;
                }
            }
            deduction->addSubformula( llBs.begin()->second.nextWeakerBound->pAsConstraint() );
            addDeduction( deduction );
            #ifdef SMTRAT_DEVOPTION_Statistics
            mpStatistics->addRefinement();
            mpStatistics->addDeduction();
            #endif
            vector<const LRABound* >* toDelete = llBs.begin()->second.premise;
            llBs.erase( llBs.begin() );
            delete toDelete;
        }
        map<LRAVariable*, typename LRATableau::LearnedBound>& luBs = mTableau.rLearnedUpperBounds();
        while( !luBs.empty() )
        {
            Formula* deduction = new Formula( OR );
            for( auto bound = luBs.begin()->second.premise->begin(); bound != luBs.begin()->second.premise->end(); ++bound )
            {
                auto originIterB = (*bound)->origins().begin()->begin();
                while( originIterB != (*bound)->origins().begin()->end() )
                {
                    deduction->addSubformula( new Formula( NOT ) );
                    deduction->back()->addSubformula( (*originIterB)->pConstraint() );
                    ++originIterB;
                }
            }
            deduction->addSubformula( luBs.begin()->second.nextWeakerBound->pAsConstraint() );
            addDeduction( deduction );
            #ifdef SMTRAT_DEVOPTION_Statistics
            mpStatistics->addRefinement();
            mpStatistics->addDeduction();
            #endif
            vector<const LRABound* >* toDelete = luBs.begin()->second.premise;
            luBs.erase( luBs.begin() );
            delete toDelete;
        }
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
                addSubformulaToPassedFormula( new Formula( bound.pAsConstraint() ), bound.origins() );
                bound.pInfo()->position = mpPassedFormula->last();
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
     * @return false, if a conflict occurs;
     *          true, otherwise.
     */
    bool LRAModule::activateBound( const LRABound* _bound, const set<const Formula*>& _formulas )
    {
        bool result = true;
        // If the bounds constraint has already been passed to the backend, add the given formulas to it's origins
        if( _bound->pInfo()->position != mpPassedFormula->end() )
            addOrigin( *_bound->pInfo()->position, _formulas );
        mTableau.activateBound( _bound, _formulas );
        const LRAVariable& var = _bound->variable();
        if( _bound->isUpperBound() )
        {
            if( *var.pInfimum() > _bound->limit() && !_bound->deduced() )
            {
                set<const Formula*> infsubset = set<const Formula*>();
                infsubset.insert( _bound->pOrigins()->begin()->begin(), _bound->pOrigins()->begin()->end() );
                infsubset.insert( var.pInfimum()->pOrigins()->back().begin(), var.pInfimum()->pOrigins()->back().end() );
                mInfeasibleSubsets.push_back( infsubset );
                result = false;
            }
            if( *var.pSupremum() > *_bound )
            {
                if( !var.pSupremum()->isInfinite() )
                    mBoundCandidatesToPass.push_back( var.pSupremum() );
                mBoundCandidatesToPass.push_back( _bound );
            }
        }
        if( _bound->isLowerBound() )
        {
            if( *var.pSupremum() < _bound->limit() && !_bound->deduced() )
            {
                set<const Formula*> infsubset = set<const Formula*>();
                infsubset.insert( _bound->pOrigins()->begin()->begin(), _bound->pOrigins()->begin()->end() );
                infsubset.insert( var.pSupremum()->pOrigins()->back().begin(), var.pSupremum()->pOrigins()->back().end() );
                mInfeasibleSubsets.push_back( infsubset );
                result = false;
            }
            if( *var.pInfimum() < *_bound )
            {
                if( !var.pInfimum()->isInfinite() )
                    mBoundCandidatesToPass.push_back( var.pInfimum() );
                mBoundCandidatesToPass.push_back( _bound );
            }
        }
        return result;
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
                    if( (*currentBound)->pInfo()->exists )
                    {
                        Formula* deduction = new Formula( OR );
                        deduction->addSubformula( new Formula( NOT ) );
                        deduction->back()->addSubformula( (*currentBound)->pAsConstraint() );
                        deduction->addSubformula( _boundNeq ? _bound->neqRepresentation() : _bound->pAsConstraint() );
                        addDeduction( deduction );
                        #ifdef SMTRAT_DEVOPTION_Statistics
                        mpStatistics->addDeduction();
                        #endif
                    }
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
                        Formula* deduction = new Formula( OR );
                        deduction->addSubformula( new Formula( NOT ) );
                        deduction->back()->addSubformula( _bound->pAsConstraint() );
                        deduction->addSubformula( (*currentBound)->pAsConstraint() );
                        addDeduction( deduction );
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
                        Formula* deduction = new Formula( OR );
                        deduction->addSubformula( new Formula( NOT ) );
                        deduction->back()->addSubformula( _bound->pAsConstraint() );
                        deduction->addSubformula( (*currentBound)->pAsConstraint() );
                        addDeduction( deduction );
                        #ifdef SMTRAT_DEVOPTION_Statistics
                        mpStatistics->addDeduction();
                        #endif
                    }
                    ++currentBound;
                }
                ++currentBound;
            }
            if( _bound->type() != LRABound::Type::EQUAL )
            {
                while( currentBound != lraVar.lowerbounds().end() )
                {
                    if( (*currentBound)->pInfo()->exists )
                    {
                        Formula* deduction = new Formula( OR );
                        deduction->addSubformula( new Formula( NOT ) );
                        deduction->back()->addSubformula( (*currentBound)->pAsConstraint() );
                        deduction->addSubformula( _boundNeq ? _bound->neqRepresentation() : _bound->pAsConstraint() );
                        addDeduction( deduction );
                        #ifdef SMTRAT_DEVOPTION_Statistics
                        mpStatistics->addDeduction();
                        #endif
                    }
                    ++currentBound;
                }
            }
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
        Formula* deduction = new Formula( OR );
        deduction->addSubformula( new Formula( NOT ) );
        deduction->back()->addSubformula( _caseA.pAsConstraint() );
        deduction->addSubformula( new Formula( NOT ) );
        deduction->back()->addSubformula( _caseBneq ? _caseB.neqRepresentation() : _caseB.pAsConstraint() );
        addDeduction( deduction );
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
            mTableau.setSize( mTableau.slackVars().size(), mTableau.originalVars().size(), mLinearConstraints.size() );
            #ifdef LRA_USE_PIVOTING_STRATEGY
            mTableau.setBlandsRuleStart( 1000 );//(unsigned) mTableau.columns().size() );
            #endif
        }
    }
    
    #ifdef LRA_GOMORY_CUTS
    /**
     * 
     * @return True, if a branching occurred.
     *          False, otherwise.
     */
    bool LRAModule::gomory_cut()
    {
        EvalRationalMap rMap_ = getRationalModel();
        vector<const Constraint*> constr_vec = vector<const Constraint*>();
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
                    const Constraint* gomory_constr = mTableau.gomoryCut(ass, basicVar, constr_vec);
                    if( gomory_constr != NULL )
                    {
                        Formula* deductionA = new Formula(OR);
                        auto vec_iter = constr_vec.begin();
                        while(vec_iter != constr_vec.end())
                        {
                            Formula* notItem = new Formula(NOT);
                            notItem->addSubformula(*vec_iter);
                            deductionA->addSubformula(notItem);
                            ++vec_iter; 
                        } 
                        deductionA->addSubformula(gomory_constr);
                        addDeduction(deductionA);   
                    }                                                                
                }
            }    
        }                            
        return !all_int;
    }
    #endif
    
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
        unsigned i=0;
        /*
        for( auto nbVar = mTableau.columns().begin(); nbVar != mTableau.columns().end(); ++nbVar )
        {
            dc_Tableau.newNonbasicVariable( new Polynomial( (*mTableau.columns().at(i)).expression() ) );
            //dc_Tableau.newNonbasicVariable( new Polynomial( mTableau.columns().at(i)->mName->expression() ) );
            ++i;
        }  
        */                         
        size_t numRows = mTableau.rows().size();
        size_t dc_count = 0;
        vector<size_t> dc_positions;
        vector<LRAEntryType> lcm_rows;
        for( size_t i = 0; i < numRows; ++i )
        {
            vector<size_t> non_basic_vars_positions;
            vector<LRAEntryType> coefficients;
            LRAEntryType lcmOfCoeffDenoms = 1;
            LRAEntryType max_value = 0;
            const Constraint* dc_constraint = mTableau.isDefining( i, non_basic_vars_positions, coefficients, lcmOfCoeffDenoms, max_value );
            if( dc_constraint != NULL  )
            {
                cout << "Found defining constraint!" << endl;
                dc_count++;
                dc_positions.push_back(i);
                lcm_rows.push_back( lcmOfCoeffDenoms );
                assert( !non_basic_vars_positions.empty() );
                vector< LRAVariable* > non_basic_vars;
                size_t j=0;
                auto pos = non_basic_vars_positions.begin();
                /*
                for( auto column = dc_Tableau.columns().begin(); column != dc_Tableau.columns().end(); ++column )
                {
                    LRAVariable* nonbasicVar = mTableau.columns().at(j);
                    if( nonbasicVar->position() == *pos )
                    {                                                                                    
                        assert( pos != non_basic_vars_positions.end() );
                        non_basic_vars.push_back( nonbasicVar );
                        ++pos;                                            
                    }
                    ++j;    
                }      
                */          
                //dc_Tableau.newBasicVariable( help, non_basic_vars, coefficients );
                cout << "Inserted it!" << endl;
                dc_Tableau.newBound(dc_constraint);
                dc_Tableau.print();
                /*
                if( lcmOfCoeffDenoms != 1 )
                {
                    dc_Tableau.multiplyRow( dc_count-1, lcmOfCoeffDenoms ); 
                } 
                */   
            }   
        }
        dc_Tableau.print();
        if( dc_Tableau.rows().size() > 0 )
        {
            #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
            cout << "Defining constraint:" << endl;
            dc_Tableau.print();   
            #endif

            // At least one DC exists -> Construct and embed it.
            vector<size_t> diagonals;    
            vector<size_t>& diagonals_ref = diagonals;                            
            dc_Tableau.calculate_hermite_normalform( diagonals_ref );
            
            #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
            cout << "HNF of defining constraints:" << endl;
            dc_Tableau.print();
            cout << "Actual order of columns:" << endl;
            for( auto iter = diagonals.begin(); iter != diagonals.end(); ++iter ) printf( "%u", *iter );
            #endif

            dc_Tableau.invert_HNF_Matrix( diagonals );
            bool creatable = false;
            Polynomial cut;
            for( size_t i = 0; i < dc_positions.size(); ++i )
            {
                vector<LRAEntryType> coefficients2;
                vector<bool> non_basics_proof;
                vector< LRAVariable* > non_basic_vars2;
                LRABound* upper_lower_bound;
                creatable = dc_Tableau.create_cut_from_proof( dc_Tableau, mTableau, i, lcm_rows.at(i), coefficients2, non_basics_proof, cut, diagonals, dc_positions, upper_lower_bound );
                Polynomial* pcut = new Polynomial( cut );
//                #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
                #ifdef MODULE_VERBOSE_INTEGERS
                cout << "Proof of unsatisfiability:  " << *pcut << " = 0" << endl;
                #endif
//                #endif
                unsigned j=0;
                for( auto vector_iterator = non_basics_proof.begin(); vector_iterator != non_basics_proof.end(); ++vector_iterator )
                {
                    if( *vector_iterator )
                    {
                        non_basic_vars2.push_back( dc_Tableau.columns().at(diagonals.at(j)) );
                    }
                    ++j;
                }
                if( creatable )
                {
                    #ifndef LRA_DEBUG_CUTS_FROM_PROOFS
                    //mTableau.newBasicVariable( pcut, non_basic_vars2, coefficients2 );
                    #else
                    //auto var2 = mTableau.newBasicVariable( pcut, non_basic_vars2, coefficients2 );
                    cout << "After adding proof of unsatisfiability:" << endl;
                    //var2->print();
                    //var2->printAllBounds();
                    mTableau.print();
                    cout << "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~" << endl;
                    #endif
                    //mTableau.rows().at(mTableau.rows().size()-1).mName->setSupremum(upper_bound);
                    //mTableau.rows().at(mTableau.rows().size()-1).mName->setSupremum(lower_bound);
                    return true;
                }
            }
            #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
            cout << "Found no proof of unsatisfiability!" << endl;
            #endif
        }
        #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
        else
            cout << "No defining constraint!" << endl;
        cout << "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~" << endl;
        #endif
        branchAt( Polynomial( var->first ), map_iterator->second );
        return true;
    }
    #endif
    
    /**
     * @return true, if a branching occurred.
     *         false, otherwise.
     */
    bool LRAModule::branch_and_bound()
    {
        EvalRationalMap _rMap = getRationalModel();
        auto map_iterator = _rMap.begin();
        for( auto var = mTableau.originalVars().begin(); var != mTableau.originalVars().end(); ++var )
        {
            assert( var->first == map_iterator->first );
            Rational& ass = map_iterator->second; 
            if( var-> first.getType() == carl::VariableType::VT_INT && !carl::isInteger( ass ) )
            {
                #ifdef MODULE_VERBOSE_INTEGERS
                this->printRationalModel();
                #endif
                branchAt( Polynomial( var->first ), ass );
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
}    // namespace smtrat

