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
 * @version 2013-02-07
 * Created on April 5th, 2012, 3:22 PM
 */


#include "LRAModule.h"
#include <iostream>

//#define DEBUG_LRA_MODULE
#define LRA_SIMPLE_THEORY_PROPAGATION
#define LRA_ONE_REASON
//#define LRA_BRANCH_AND_BOUND
//#define LRA_GOMORY_CUTS
using namespace std;
using namespace lra;
using namespace GiNaC;
using namespace GiNaCRA;

namespace smtrat
{
    /**
     * Constructor
     */
    LRAModule::LRAModule( ModuleType _type, const Formula* const _formula, RuntimeSettings* settings, Conditionals& _conditionals, Manager* const _manager ):
        Module( _type, _formula, _conditionals, _manager ),
        mInitialized( false ),
        mAssignmentFullfilsNonlinearConstraints( false ),
        mTableau( mpPassedFormula->end() ),
        mLinearConstraints(),
        mNonlinearConstraints(),
        mActiveResolvedNEQConstraints(),
        mActiveUnresolvedNEQConstraints(),
        mResolvedNEQConstraints(),
        mOriginalVars(),
        mSlackVars(),
        mConstraintToBound(),
        mBoundToUnequalConstraintMap(),
        mBoundCandidatesToPass()
    {}

    /**
     * Destructor:
     */
    LRAModule::~LRAModule()
    {
        while( !mConstraintToBound.empty() )
        {
            vector< const Bound* >* toDelete = mConstraintToBound.begin()->second;
            mConstraintToBound.erase( mConstraintToBound.begin() );
            if( toDelete != NULL ) delete toDelete;
        }
        while( !mOriginalVars.empty() )
        {
            const ex* exToDelete = mOriginalVars.begin()->first;
            mOriginalVars.erase( mOriginalVars.begin() );
            delete exToDelete;
        }
        while( !mSlackVars.empty() )
        {
            const ex* exToDelete = mSlackVars.begin()->first;
            mSlackVars.erase( mSlackVars.begin() );
            delete exToDelete;
        }
    }

    /**
     * Methods:
     */

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
        if( !_constraint->variables().empty() && _constraint->isLinear() )
        {
            bool elementInserted = mLinearConstraints.insert( _constraint ).second;
            if( elementInserted && mInitialized )
            {
                initialize( _constraint );
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
        if( (*_subformula)->getType() == REALCONSTRAINT )
        {
            if( !mInitialized ) initialize();

            const Constraint* constraint  = (*_subformula)->pConstraint();
            int               consistency = constraint->isConsistent();
            if( consistency == 2 )
            {
                mAssignmentFullfilsNonlinearConstraints = false;
                if( constraint->isLinear() )
                {
                    if( (*_subformula)->constraint().relation() != CR_NEQ )
                    {
                        vector< const Bound* >* bounds = mConstraintToBound[constraint];
                        assert( bounds != NULL );

                        set<const Formula*> originSet = set<const Formula*>();
                        originSet.insert( *_subformula );
                        activateBound( *bounds->begin(), originSet );

                        auto unequalCons = mBoundToUnequalConstraintMap.find( *bounds->begin() );
                        if( unequalCons != mBoundToUnequalConstraintMap.end() )
                        {
                            auto pos = mActiveUnresolvedNEQConstraints.find( unequalCons->second );
                            if( pos != mActiveUnresolvedNEQConstraints.end() )
                            {
                                auto entry = mActiveResolvedNEQConstraints.insert( *pos );
                                removeSubformulaFromPassedFormula( pos->second.position );
                                entry.first->second.position = mpPassedFormula->end();
                                mActiveUnresolvedNEQConstraints.erase( pos );
                            }
                        }

                        assert( mInfeasibleSubsets.empty() || !mInfeasibleSubsets.begin()->empty() );
                        return mInfeasibleSubsets.empty() || !mNonlinearConstraints.empty();
                    }
                    else
                    {
                        vector< const Bound* >* bounds = mConstraintToBound[constraint];
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
            else if( consistency == 0 )
            {
                set< const Formula* > infSubSet = set< const Formula* >();
                infSubSet.insert( *_subformula );
                mInfeasibleSubsets.push_back( infSubSet );
                foundAnswer( False );
                return false;
            }
            else
            {
                return true;
            }
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
        if( (*_subformula)->getType() == REALCONSTRAINT )
        {
            // Remove the mapping of the constraint to the sub-formula in the received formula
            const Constraint* constraint = (*_subformula)->pConstraint();
            if( constraint->isConsistent() == 2 )
            {
                if( constraint->isLinear() )
                {
                    if( (*_subformula)->constraint().relation() != CR_NEQ )
                    {
                        // Deactivate the bounds regarding the given constraint
                        vector< const Bound* >* bounds = mConstraintToBound[constraint];
                        assert( bounds != NULL );
                        auto bound = bounds->begin();
                        while( bound != bounds->end() )
                        {
                            if( !(*bound)->origins().empty() )
                            {
                                auto originSet = (*bound)->pOrigins()->begin();
                                while( originSet != (*bound)->origins().end() )
                                {
                                    if( originSet->find( *_subformula ) != originSet->end() ) originSet = (*bound)->pOrigins()->erase( originSet );
                                    else ++originSet;
                                }
                                if( (*bound)->origins().empty() )
                                {
                                    auto unequalCons = mBoundToUnequalConstraintMap.find( *bound );
                                    if( unequalCons != mBoundToUnequalConstraintMap.end() )
                                    {
                                        vector< const Bound* >* uebounds = mConstraintToBound[unequalCons->second];
                                        assert( uebounds != NULL );
                                        assert( uebounds->size() == 2 );
                                        if( !(*uebounds)[0]->isActive() && !(*uebounds)[1]->isActive() )
                                        {
                                            auto pos = mActiveResolvedNEQConstraints.find( unequalCons->second );
                                            if( pos != mActiveResolvedNEQConstraints.end() )
                                            {
                                                auto entry = mActiveUnresolvedNEQConstraints.insert( *pos );
                                                mActiveResolvedNEQConstraints.erase( pos );
                                                addSubformulaToPassedFormula( new Formula( entry.first->first ), entry.first->second.origin );
                                                entry.first->second.position = mpPassedFormula->last();
                                            }
                                        }
                                    }
                                    (*bound)->pVariable()->deactivateBound( *bound, mpPassedFormula->end() );
                                    if( !(*bound)->pVariable()->pSupremum()->isInfinite() )
                                    {
                                        mBoundCandidatesToPass.push_back( (*bound)->pVariable()->pSupremum() );
                                    }
                                    if( !(*bound)->pVariable()->pInfimum()->isInfinite() )
                                    {
                                        mBoundCandidatesToPass.push_back( (*bound)->pVariable()->pInfimum() );
                                    }
                                    if( ((*bound)->isUpperBound() && (*bound)->variable().pSupremum()->isInfinite())
                                        || ((*bound)->isLowerBound() && (*bound)->variable().pInfimum()->isInfinite()) )
                                    {
                                        if( (*bound)->variable().isBasic() )
                                        {
                                            mTableau.decrementBasicActivity( (*bound)->variable() );
                                        }
                                        else
                                        {
                                            mTableau.decrementNonbasicActivity( (*bound)->variable() );
                                        }
                                    }
                                }
                            }
                            if( bound != bounds->begin() )
                            {
                                bound = bounds->erase( bound );
                            }
                            else
                            {
                                ++bound;
                            }
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
                    ConstraintSet::iterator nonLinearConstraint = mNonlinearConstraints.find( constraint );
                    assert( nonLinearConstraint != mNonlinearConstraints.end() );
                    mNonlinearConstraints.erase( nonLinearConstraint );
                }
            }
        }
        Module::removeSubformula( _subformula );
    }

    /**
     * Checks the consistency of the so far received constraints.
     *
     * @return True,    if the so far received constraints are consistent;
     *         False,   if the so far received constraints are inconsistent;
     *         Unknown, if this module cannot determine whether the so far received constraints are consistent or not.
     */
    Answer LRAModule::isConsistent()
    {
        #ifdef DEBUG_LRA_MODULE
        cout << "check for consistency" << endl;
        #endif
        if( !mpReceivedFormula->isRealConstraintConjunction() ) return foundAnswer( Unknown );
        if( !mInfeasibleSubsets.empty() )
        {
            return foundAnswer( False );
        }
        unsigned posNewLearnedBound = 0;
        for( ; ; )
        {
            // Check whether a module which has been called on the same instance in parallel, has found an answer.
            if( anAnswerFound() )
            {
                learnRefinements();
                return foundAnswer( Unknown );
            }
            #ifdef DEBUG_LRA_MODULE
            cout << endl;
            mTableau.printVariables( cout, "    " );
            cout << endl;
            mTableau.print( cout, 15, "    " );
            cout << endl;
            #endif

            // Find a pivoting element in the tableau.
            pair<EntryID,bool> pivotingElement = mTableau.nextPivotingElement();

            #ifdef DEBUG_LRA_MODULE
            cout << "    Next pivoting element: ";
            mTableau.printEntry( cout, pivotingElement.first );
            cout << (pivotingElement.second ? "(True)" : "(False)");
            cout << " [" << pivotingElement.first << "]" << endl;
            #endif

            // If there is no conflict.
            if( pivotingElement.second )
            {
                // If no basic variable violates its bounds (and hence no variable at all).
                if( pivotingElement.first == 0 )
                {
                    CONSTRAINT_LOCK_GUARD
                    #ifdef DEBUG_LRA_MODULE
                    cout << "True" << endl;
                    #endif
                    // If the current assignment also fulfills the nonlinear constraints.
                    if( checkAssignmentForNonlinearConstraint() )
                    {
                        // If there are no unresolved notequal-constraints, return True.
                        if( mActiveUnresolvedNEQConstraints.empty() )
                        {
                            #ifdef LRA_REFINEMENT
                            learnRefinements();
                            #endif

                            #ifdef LRA_GOMORY_CUTS
                            exmap rMap_ = getRationalModel();
                            for(auto vector_iterator = mTableau.rows().begin();vector_iterator != mTableau.rows().end();++vector_iterator)
                            {
                                ex referring_ex = vector_iterator->mName->expression();
                                auto pToEx = rMap_.find(referring_ex);
                                numeric ass = ex_to<numeric>(pToEx->second);
                                if(!ass.is_integer())
                                {
                                    //...
                                }
                            }
                            #endif

                            #ifdef LRA_BRANCH_AND_BOUND
                            exmap _rMap = getRationalModel();
                            exmap::const_iterator map_iterator = _rMap.begin();
                            for(auto var=mOriginalVars.begin();var != mOriginalVars.end() ;++var)
                            {
                                if(Formula::domain(*var->first) == INTEGER_DOMAIN)
                                {
                                   Formula* deductionA = new Formula(OR);
                                   stringstream sstream;
                                   sstream << *var->first;
                                   symtab *setOfVar = new symtab();
                                   setOfVar->insert(pair< std::string, ex >(sstream.str(),*var->first));
                                   numeric ass = ex_to<numeric>(map_iterator->second);
                                   ass = ass.to_int();
                                   const Constraint* lessEqualConstraint = Formula::newConstraint(*var->first - ass,CR_LEQ,*setOfVar);
                                   const Constraint* biggerEqualConstraint= Formula::newConstraint(*var->first - ass - 1,CR_GEQ,*setOfVar);
                                   deductionA->addSubformula(lessEqualConstraint);
                                   deductionA->addSubformula(biggerEqualConstraint);
                                   addDeduction(deductionA);
                                   return foundAnswer(Unknown);
                                }
                            ++map_iterator;
                            }
                            return foundAnswer(True);
                            #endif
                            return foundAnswer( True );
                        }
                        // Otherwise, resolve the notequal-constraints (create the lemma (p<0 or p>0) <-> p!=0 ) and return Unknown.
                        else
                        {
                            for( auto iter = mActiveUnresolvedNEQConstraints.begin(); iter != mActiveUnresolvedNEQConstraints.end(); ++iter )
                            {
                                if( mResolvedNEQConstraints.find( iter->first ) == mResolvedNEQConstraints.end() )
                                {
                                    splitUnequalConstraint( iter->first );
                                    mResolvedNEQConstraints.insert( iter->first );
                                }
                            }
                            #ifdef LRA_REFINEMENT
                            learnRefinements();
                            #endif
                            return foundAnswer( Unknown );
                        }
                    }
                    // Otherwise, check the consistency of the formula consisting of the nonlinear constraints and the tightest bounds with the backends.
                    else
                    {
                        for( auto iter = mActiveUnresolvedNEQConstraints.begin(); iter != mActiveUnresolvedNEQConstraints.end(); ++iter )
                        {
                            if( mResolvedNEQConstraints.find( iter->first ) == mResolvedNEQConstraints.end() )
                            {
                                splitUnequalConstraint( iter->first );
                                mResolvedNEQConstraints.insert( iter->first );
                            }
                        }
                        adaptPassedFormula();
                        Answer a = runBackends();
                        if( a == False )
                        {
                            getInfeasibleSubsets();
                        }
                        #ifdef LRA_REFINEMENT
                        learnRefinements();
                        #endif
                        return foundAnswer( a );
                    }
                }
                else
                {
                    // Pivot at the found pivoting entry.
                    mTableau.pivot( pivotingElement.first );
                    CONSTRAINT_LOCK_GUARD
                    // Learn all bounds which has been deduced during the pivoting process.
                    while( posNewLearnedBound < mTableau.rLearnedBounds().size() )
                    {
                        set< const Formula*> originSet = set< const Formula*>();
                        Tableau::LearnedBound& learnedBound = mTableau.rLearnedBounds()[posNewLearnedBound];
                        vector<const Bound*>& bounds = *learnedBound.premise;
                        for( auto bound = bounds.begin(); bound != bounds.end(); ++bound )
                        {
                            assert( !(*bound)->origins().empty() );
                            originSet.insert( (*bound)->origins().begin()->begin(), (*bound)->origins().begin()->end() );
                            for( auto origin = (*bound)->origins().begin()->begin(); origin != (*bound)->origins().begin()->end(); ++origin )
                            {
                                const Constraint* constraint = (*origin)->pConstraint();
                                if( constraint != NULL )
                                {
                                    vector< const Bound* >* constraintToBounds = mConstraintToBound[constraint];
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
                            vector< const Bound* >* boundVector = new vector< const Bound* >();
                            boundVector->push_back( learnedBound.newBound );
                            mConstraintToBound[newConstraint] = boundVector;
                            activateBound( learnedBound.newBound, originSet );
                        }
                        #endif
                        ++posNewLearnedBound;
                    }
                    // Maybe a easy conflict occurred with the learned bounds.
                    if( !mInfeasibleSubsets.empty() )
                    {
                        #ifdef LRA_REFINEMENT
                        learnRefinements();
                        #endif
                        return foundAnswer( False );
                    }
                }
            }
            // There is a conflict, namely a basic variable violating its bounds without any suitable non-basic variable.
            else
            {
                CONSTRAINT_LOCK_GUARD
                // Create the infeasible subsets.
                mInfeasibleSubsets.clear();
                #ifdef LRA_ONE_REASON
                vector< const Bound* > conflict = mTableau.getConflict( pivotingElement.first );
                set< const Formula* > infSubSet = set< const Formula* >();
                for( auto bound = conflict.begin(); bound != conflict.end(); ++bound )
                {
                    assert( (*bound)->isActive() );
                    infSubSet.insert( (*bound)->pOrigins()->begin()->begin(), (*bound)->pOrigins()->begin()->end() );
                }
                mInfeasibleSubsets.push_back( infSubSet );
                #else
                vector< set< const Bound* > > conflictingBounds = mTableau.getConflictsFrom( pivotingElement.first );
                for( auto conflict = conflictingBounds.begin(); conflict != conflictingBounds.end(); ++conflict )
                {
                    set< const Formula* > infSubSet = set< const Formula* >();
                    for( auto bound = conflict->begin(); bound != conflict->end(); ++bound )
                    {
                        assert( (*bound)->isActive() );
                        infSubSet.insert( *(*bound)->pOrigins()->begin() );
                    }
                    mInfeasibleSubsets.push_back( infSubSet );
                }
                #endif
                #ifdef LRA_REFINEMENT
                learnRefinements();
                #endif
                // Return False.
                #ifdef DEBUG_LRA_MODULE
                cout << "False" << endl;
                #endif
                return foundAnswer( False );
            }
        }
        assert( false );
        #ifdef LRA_REFINEMENT
        learnRefinements();
        #endif
        return foundAnswer( True );
    }

    /**
     * Updates the current assignment into the model. Note, that this is a unique but symbolic assignment still containing delta as a variable.
     */
    void LRAModule::updateModel()
    {
        mModel.clear();
        if( solverState() == True )
        {
            if( mAssignmentFullfilsNonlinearConstraints )
            {
                for( ExVariableMap::const_iterator originalVar = mOriginalVars.begin(); originalVar != mOriginalVars.end(); ++originalVar )
                {
                    stringstream outA;
                    outA << *originalVar->first;
                    stringstream outB;
                    outB << originalVar->second->assignment().mainPart();
                    if( originalVar->second->assignment().deltaPart() != 0 )
                    {
                        outB << "+delta_" << mId << "*" << originalVar->second->assignment().deltaPart();
                    }
                    mModel.insert( pair< const string, string >( outA.str(), outB.str() ) );
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
    exmap LRAModule::getRationalModel() const
    {
        exmap result = exmap();
        if( mInfeasibleSubsets.empty() )
        {
            /*
            * Check whether the found satisfying assignment is by coincidence a
            * satisfying assignment of the non linear constraints
            */
            numeric minDelta = -1;
            numeric curDelta = 0;
            Variable* variable = NULL;
            /*
            * For all slack variables find the minimum of all (c2-c1)/(k1-k2), where ..
            */
            for( auto originalVar = mOriginalVars.begin(); originalVar != mOriginalVars.end(); ++originalVar )
            {
                variable = originalVar->second;
                const Value& assValue = variable->assignment();
                const Bound& inf = variable->infimum();
                if( !inf.isInfinite() )
                {
                    /*
                    * .. the supremum is c2+k2*delta, the variable assignment is c1+k1*delta, c1<c2 and k1>k2.
                    */
                    if( inf.limit().mainPart() < assValue.mainPart() && inf.limit().deltaPart() > assValue.deltaPart() )
                    {
                        curDelta = ( assValue.mainPart() - inf.limit().mainPart() ) / ( inf.limit().deltaPart() - assValue.deltaPart() );
                        if( minDelta < 0 || curDelta < minDelta )
                        {
                            minDelta = curDelta;
                        }
                    }
                }
                const Bound& sup = variable->supremum();
                if( !sup.isInfinite() )
                {
                    /*
                    * .. the infimum is c1+k1*delta, the variable assignment is c2+k2*delta, c1<c2 and k1>k2.
                    */
                    if( sup.limit().mainPart() > assValue.mainPart() && sup.limit().deltaPart() < assValue.deltaPart() )
                    {
                        curDelta = ( sup.limit().mainPart() - assValue.mainPart() ) / ( assValue.deltaPart() - sup.limit().deltaPart() );
                        if( minDelta < 0 || curDelta < minDelta )
                        {
                            minDelta = curDelta;
                        }
                    }
                }
            }
            /*
            * For all slack variables find the minimum of all (c2-c1)/(k1-k2), where ..
            */
            for( auto slackVar = mSlackVars.begin(); slackVar != mSlackVars.end(); ++slackVar )
            {
                variable = slackVar->second;
                const Value& assValue = variable->assignment();
                const Bound& inf = variable->infimum();
                if( !inf.isInfinite() )
                {
                    /*
                    * .. the infimum is c1+k1*delta, the variable assignment is c2+k2*delta, c1<c2 and k1>k2.
                    */
                    if( inf.limit().mainPart() < assValue.mainPart() && inf.limit().deltaPart() > assValue.deltaPart() )
                    {
                        curDelta = ( assValue.mainPart() - inf.limit().mainPart() ) / ( inf.limit().deltaPart() - assValue.deltaPart() );
                        if( minDelta < 0 || curDelta < minDelta )
                        {
                            minDelta = curDelta;
                        }
                    }
                }
                const Bound& sup = variable->supremum();
                if( !sup.isInfinite() )
                {
                    /*
                    * .. the supremum is c2+k2*delta, the variable assignment is c1+k1*delta, c1<c2 and k1>k2.
                    */
                    if( sup.limit().mainPart() > assValue.mainPart() && sup.limit().deltaPart() < assValue.deltaPart() )
                    {
                        curDelta = ( sup.limit().mainPart() - assValue.mainPart() ) / ( assValue.deltaPart() - sup.limit().deltaPart() );
                        if( minDelta < 0 || curDelta < minDelta )
                        {
                            minDelta = curDelta;
                        }
                    }
                }
            }

            curDelta = minDelta < 0 ? 1 : minDelta;
            /*
            * Calculate the rational assignment of all original variables.
            */
            for( auto var = mOriginalVars.begin(); var != mOriginalVars.end(); ++var )
            {
                const Value& value = var->second->assignment();
                result.insert( pair< ex, ex >( *var->first, ex( value.mainPart() + value.deltaPart() * curDelta ) ) );
            }
        }
        return result;
    }

    /**
     * Returns the bounds of the variables as intervals.
     *
     * @return The bounds of the variables as intervals.
     */
    evalintervalmap LRAModule::getVariableBounds() const
    {
        evalintervalmap result = evalintervalmap();
        for( auto iter = mOriginalVars.begin(); iter != mOriginalVars.end(); ++iter )
        {
            const Variable& var = *iter->second;
            Interval::BoundType lowerBoundType;
            numeric lowerBoundValue;
            Interval::BoundType upperBoundType;
            numeric upperBoundValue;
            if( var.infimum().isInfinite() )
            {
                lowerBoundType = Interval::INFINITY_BOUND;
                lowerBoundValue = 0;
            }
            else
            {
                lowerBoundType = var.infimum().isWeak() ? Interval::WEAK_BOUND : Interval::STRICT_BOUND;
                lowerBoundValue = var.infimum().limit().mainPart();
            }
            if( var.supremum().isInfinite() )
            {
                upperBoundType = Interval::INFINITY_BOUND;
                upperBoundValue = 0;
            }
            else
            {
                upperBoundType = var.supremum().isWeak() ? Interval::WEAK_BOUND : Interval::STRICT_BOUND;
                upperBoundValue = var.supremum().limit().mainPart();
            }
            Interval interval = Interval( lowerBoundValue, lowerBoundType, upperBoundValue, upperBoundType );
            result.insert( pair< symbol, Interval >( ex_to< symbol >( *iter->first ), interval ) );
        }
        return result;
    }

    #ifdef LRA_REFINEMENT
    /**
     * Adds the refinements learned during pivoting to the deductions.
     */
    void LRAModule::learnRefinements()
    {
        CONSTRAINT_LOCK_GUARD
        vector<Tableau::LearnedBound>& lBs = mTableau.rLearnedBounds();
        while( !lBs.empty() )
        {
            auto originsIterA = lBs.back().nextWeakerBound->origins().begin();
            while( originsIterA != lBs.back().nextWeakerBound->origins().end() )
            {
                // TODO: Learn also those deductions with a conclusion containing more than one constraint.
                //       This must be hand over via a non clause formula and could introduce new
                //       Boolean variables.
                if( originsIterA->size() == 1 )
                {
                    if( originsIterA != lBs.back().nextWeakerBound->origins().end() )
                    {
                        auto originIterA = originsIterA->begin();
                        while( originIterA != originsIterA->end() )
                        {
                            Formula* deduction = new Formula( OR );
                            for( auto bound = lBs.back().premise->begin(); bound != lBs.back().premise->end(); ++bound )
                            {
                                auto originIterB = (*bound)->origins().begin()->begin();
                                while( originIterB != (*bound)->origins().begin()->end() )
                                {
                                    deduction->addSubformula( new Formula( NOT ) );
                                    deduction->back()->addSubformula( (*originIterB)->pConstraint() );
                                    ++originIterB;
                                }
                            }
                            deduction->addSubformula( (*originIterA)->pConstraint() );
                            addDeduction( deduction );
                            ++originIterA;
                        }
                    }
                }
                ++originsIterA;
            }
            vector<const Bound* >* toDelete = lBs.back().premise;
            lBs.pop_back();
            delete toDelete;
        }
    }
    #endif

    /**
     * Checks whether an iterator is in a formula. Only used in an assertion.
     *
     * @param _iter The iterator supposed to be in the formula.
     * @param _formula The formula, in which the iterator is supposed to be.
     *
     * @return True, if the given iterator is in the given formula; False, otherwise.
     */
    bool iterInFormula( Formula::const_iterator _iter, const Formula& _formula )
    {
        if( _formula.isBooleanCombination() )
        {
            for( Formula::const_iterator iter = _formula.begin(); iter != _formula.end(); ++iter )
            {
                if( iter == _iter ) return true;
            }
        }
        return false;
    }

    /**
     * Adapt the passed formula, such that it consists of the finite infimums and supremums
     * of all variables and the non linear constraints.
     */
    void LRAModule::adaptPassedFormula()
    {
        while( !mBoundCandidatesToPass.empty() )
        {
            const Bound& bound = *mBoundCandidatesToPass.back();
            if( bound.pInfo()->updated > 0 )
            {
                addSubformulaToPassedFormula( new Formula( bound.pAsConstraint() ), bound.origins() );
                bound.pInfo()->position = mpPassedFormula->last();
                bound.pInfo()->updated = 0;
            }
            else if( bound.pInfo()->updated < 0 )
            {
                assert( iterInFormula( bound.pInfo()->position, *mpPassedFormula ) );
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
            exmap assignments = getRationalModel();
            /*
             * Check whether the assignment satisfies the non linear constraints.
             */
            CONSTRAINT_LOCK_GUARD
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
     * Adds the following lemmas for the given constraint p!=0
     *
     *      (p!=0 <-> (p<0 or p>0))
     * and  not(p<0 and p>0)
     *
     * @param _unequalConstraint A constraint having the relation symbol !=.
     */
    void LRAModule::splitUnequalConstraint( const Constraint* _unequalConstraint )
    {
        CONSTRAINT_LOCK_GUARD
        assert( _unequalConstraint->relation() == CR_NEQ );
        const Constraint* lessConstraint = Formula::newConstraint( _unequalConstraint->lhs(), CR_LESS, _unequalConstraint->variables() );
        const Constraint* greaterConstraint = Formula::newConstraint( _unequalConstraint->lhs(), CR_GREATER, _unequalConstraint->variables() );
        // (not p!=0 or p<0 or p>0)
        Formula* deductionA = new Formula( OR );
        Formula* notConstraint = new Formula( NOT );
        notConstraint->addSubformula( _unequalConstraint );
        deductionA->addSubformula( notConstraint );
        deductionA->addSubformula( lessConstraint );
        deductionA->addSubformula( greaterConstraint );
        addDeduction( deductionA );
        // (not p<0 or p!=0)
        Formula* deductionB = new Formula( OR );
        Formula* notLessConstraint = new Formula( NOT );
        notLessConstraint->addSubformula( lessConstraint );
        deductionB->addSubformula( notLessConstraint );
        deductionB->addSubformula( _unequalConstraint );
        addDeduction( deductionB );
        // (not p>0 or p!=0)
        Formula* deductionC = new Formula( OR );
        Formula* notGreaterConstraint = new Formula( NOT );
        notGreaterConstraint->addSubformula( greaterConstraint );
        deductionC->addSubformula( notGreaterConstraint );
        deductionC->addSubformula( _unequalConstraint );
        addDeduction( deductionC );
        // (not p>0 or not p>0)
        Formula* deductionD = new Formula( OR );
        Formula* notGreaterConstraintB = new Formula( NOT );
        notGreaterConstraintB->addSubformula( greaterConstraint );
        Formula* notLessConstraintB = new Formula( NOT );
        notLessConstraintB->addSubformula( lessConstraint );
        deductionD->addSubformula( notGreaterConstraintB );
        deductionD->addSubformula( notLessConstraintB );
        addDeduction( deductionD );
    }

    // (x-i<=0 or x-i-1>=0)   wobei wir das rationale assignment x -> r, i=abs(r)

    /**
     * Activate the given bound and update the supremum, the infimum and the assignment of
     * variable to which the bound belongs.
     *
     * @param _bound The bound to activate.
     * @param _formulas The constraints which form this bound.
     * @return False, if a conflict occurs;
     *         True, otherwise.
     */
    bool LRAModule::activateBound( const Bound* _bound, set<const Formula*>& _formulas )
    {
        bool result = true;
        _bound->pOrigins()->push_back( _formulas );
        if( _bound->pInfo()->position != mpPassedFormula->end() )
        {
            addOrigin( *_bound->pInfo()->position, _formulas );
        }
        const Variable& var = _bound->variable();
        if( (_bound->isUpperBound() && var.pSupremum()->isInfinite()) )
        {
            if( var.isBasic() )
            {
                mTableau.incrementBasicActivity( var );
            }
            else
            {
                mTableau.incrementNonbasicActivity( var );
            }
        }
        if( (_bound->isLowerBound() && var.pInfimum()->isInfinite()) )
        {
            if( var.isBasic() )
            {
                mTableau.incrementBasicActivity( var );
            }
            else
            {
                mTableau.incrementNonbasicActivity( var );
            }
        }
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
                {
                    mBoundCandidatesToPass.push_back( var.pSupremum() );
                }
                mBoundCandidatesToPass.push_back( _bound );
                _bound->pVariable()->setSupremum( _bound );

                if( result && !var.isBasic() && (*var.pSupremum() < var.assignment()) )
                {
                    mTableau.updateBasicAssignments( var.position(), Value( (*var.pSupremum()).limit() - var.assignment() ) );
                    _bound->pVariable()->rAssignment() = (*var.pSupremum()).limit();
                }
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
                {
                    mBoundCandidatesToPass.push_back( var.pInfimum() );
                }
                mBoundCandidatesToPass.push_back( _bound );
                _bound->pVariable()->setInfimum( _bound );

                if( result && !var.isBasic() && (*var.pInfimum() > var.assignment()) )
                {
                    mTableau.updateBasicAssignments( var.position(), Value( (*var.pInfimum()).limit() - var.assignment() ) );
                    _bound->pVariable()->rAssignment() = (*var.pInfimum()).limit();
                }
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
    void LRAModule::setBound( Variable& _var, bool _constraintInverted, const numeric& _boundValue, const Constraint* _constraint )
    {
        CONSTRAINT_LOCK_GUARD
        if( _constraint->relation() == CR_EQ )
        {
            // TODO: Take value from an allocator to assure the values are located close to each other in the memory.
            Value* value  = new Value( _boundValue );
            pair<const Bound* ,pair<const Bound*, const Bound*> > result = _var.addEqualBound( value, mpPassedFormula->end(), _constraint );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            findSimpleConflicts( *result.first );
            #endif
            vector< const Bound* >* boundVector = new vector< const Bound* >();
            boundVector->push_back( result.first );
            mConstraintToBound[_constraint] = boundVector;
            #ifdef LRA_SIMPLE_THEORY_PROPAGATION
            if( result.second.first != NULL && !result.second.first->isInfinite() )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( _constraint );
                deduction->addSubformula( result.second.first->pAsConstraint() );
                addDeduction( deduction );
            }
            if( result.second.first != NULL && !result.second.first->isInfinite() )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( _constraint );
                deduction->addSubformula( result.second.first->pAsConstraint() );
                addDeduction( deduction );
            }
            if( result.second.second != NULL && !result.second.second->isInfinite() )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( _constraint );
                deduction->addSubformula( result.second.second->pAsConstraint() );
                addDeduction( deduction );
            }
            if( result.second.second != NULL && !result.second.second->isInfinite() )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( _constraint );
                deduction->addSubformula( result.second.second->pAsConstraint() );
                addDeduction( deduction );
            }
            #endif
        }
        else if( _constraint->relation() == CR_LEQ )
        {
            Value* value = new Value( _boundValue );
            pair<const Bound*,pair<const Bound*, const Bound*> > result = _constraintInverted ? _var.addLowerBound( value, mpPassedFormula->end(), _constraint ) : _var.addUpperBound( value, mpPassedFormula->end(), _constraint );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            findSimpleConflicts( *result.first );
            #endif
            vector< const Bound* >* boundVector = new vector< const Bound* >();
            boundVector->push_back( result.first );
            mConstraintToBound[_constraint] = boundVector;
            #ifdef LRA_SIMPLE_THEORY_PROPAGATION
            if( result.second.first != NULL && !result.second.first->isInfinite() )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( result.second.first->pAsConstraint() );
                deduction->addSubformula( _constraint );
                addDeduction( deduction );
            }
            if( result.second.second != NULL && !result.second.second->isInfinite() )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( _constraint );
                deduction->addSubformula( result.second.second->pAsConstraint() );
                addDeduction( deduction );
            }
            #endif
        }
        else if( _constraint->relation() == CR_GEQ )
        {
            Value* value = new Value( _boundValue );
            pair<const Bound*,pair<const Bound*, const Bound*> > result = _constraintInverted ? _var.addUpperBound( value, mpPassedFormula->end(), _constraint ) : _var.addLowerBound( value, mpPassedFormula->end(), _constraint );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            findSimpleConflicts( *result.first );
            #endif
            vector< const Bound* >* boundVector = new vector< const Bound* >();
            boundVector->push_back( result.first );
            mConstraintToBound[_constraint] = boundVector;
            #ifdef LRA_SIMPLE_THEORY_PROPAGATION
            if( result.second.first != NULL && !result.second.first->isInfinite() )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( result.second.first->pAsConstraint() );
                deduction->addSubformula( _constraint );
                addDeduction( deduction );
            }
            if( result.second.second != NULL && !result.second.second->isInfinite() )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( _constraint );
                deduction->addSubformula( result.second.second->pAsConstraint() );
                addDeduction( deduction );
            }
            #endif
        }
        else
        {
            if( _constraint->relation() == CR_LESS || _constraint->relation() == CR_NEQ )
            {
                const Constraint* constraint;
                if( _constraint->relation() != CR_NEQ )
                {
                    constraint = _constraint;
                }
                else
                {
                    constraint = Formula::newConstraint( _constraint->lhs(), CR_LESS, _constraint->variables() );
                }
                Value* value = new Value( _boundValue, (_constraintInverted ? 1 : -1) );
                pair<const Bound*,pair<const Bound*, const Bound*> > result = _constraintInverted ? _var.addLowerBound( value, mpPassedFormula->end(), constraint ) : _var.addUpperBound( value, mpPassedFormula->end(), constraint );
                #ifdef LRA_SIMPLE_CONFLICT_SEARCH
                findSimpleConflicts( *result.first );
                #endif
                vector< const Bound* >* boundVector = new vector< const Bound* >();
                boundVector->push_back( result.first );
                mConstraintToBound[constraint] = boundVector;
                if( _constraint->relation() == CR_NEQ )
                {
                    vector< const Bound* >* boundVectorB = new vector< const Bound* >();
                    boundVectorB->push_back( result.first );
                    mConstraintToBound[_constraint] = boundVectorB;
                    mBoundToUnequalConstraintMap[result.first] = _constraint;
                }
                #ifdef LRA_SIMPLE_THEORY_PROPAGATION
                if( result.second.first != NULL && !result.second.first->isInfinite() )
                {
                    Formula* deduction = new Formula( OR );
                    deduction->addSubformula( new Formula( NOT ) );
                    deduction->back()->addSubformula( result.second.first->pAsConstraint() );
                    deduction->addSubformula( constraint );
                    addDeduction( deduction );
                }
                if( result.second.second != NULL && !result.second.second->isInfinite() )
                {
                    Formula* deduction = new Formula( OR );
                    deduction->addSubformula( new Formula( NOT ) );
                    deduction->back()->addSubformula( constraint );
                    deduction->addSubformula( result.second.second->pAsConstraint() );
                    addDeduction( deduction );
                }
                #endif
            }
            if( _constraint->relation() == CR_GREATER || _constraint->relation() == CR_NEQ )
            {
                const Constraint* constraint;
                if( _constraint->relation() != CR_NEQ )
                {
                    constraint = _constraint;
                }
                else
                {
                    constraint = Formula::newConstraint( _constraint->lhs(), CR_GREATER, _constraint->variables() );
                }
                Value* value = new Value( _boundValue, (_constraintInverted ? -1 : 1) );
                pair<const Bound*,pair<const Bound*, const Bound*> > result = _constraintInverted ? _var.addUpperBound( value, mpPassedFormula->end(), constraint ) : _var.addLowerBound( value, mpPassedFormula->end(), constraint );
                #ifdef LRA_SIMPLE_CONFLICT_SEARCH
                findSimpleConflicts( *result.first );
                #endif
                vector< const Bound* >* boundVector = new vector< const Bound* >();
                boundVector->push_back( result.first );
                mConstraintToBound[constraint] = boundVector;
                if( _constraint->relation() == CR_NEQ )
                {
                    mConstraintToBound[_constraint]->push_back( result.first );
                    mBoundToUnequalConstraintMap[result.first] = _constraint;
                }
                #ifdef LRA_SIMPLE_THEORY_PROPAGATION
                if( result.second.first != NULL && !result.second.first->isInfinite() )
                {
                    Formula* deduction = new Formula( OR );
                    deduction->addSubformula( new Formula( NOT ) );
                    deduction->back()->addSubformula( result.second.first->pAsConstraint() );
                    deduction->addSubformula( constraint );
                    addDeduction( deduction );
                }
                if( result.second.second != NULL && !result.second.second->isInfinite() )
                {
                    Formula* deduction = new Formula( OR );
                    deduction->addSubformula( new Formula( NOT ) );
                    deduction->back()->addSubformula( constraint );
                    deduction->addSubformula( result.second.second->pAsConstraint() );
                    addDeduction( deduction );
                }
                #endif
            }
        }
    }

    #ifdef LRA_SIMPLE_CONFLICT_SEARCH
    /**
     * Finds all conflicts between lower resp. upper bounds and the given upper
     * resp. lower bound and adds them to the deductions.
     *
     * @param _bound The bound to find conflicts for.
     */
    void LRAModule::findSimpleConflicts( const Bound& _bound )
    {
        CONSTRAINT_LOCK_GUARD
        if( _bound.deduced() ) Module::storeAssumptionsToCheck( *mpManager );
        assert( !_bound.deduced() );
        if( _bound.isUpperBound() )
        {
            const BoundSet& lbounds = _bound.variable().lowerbounds();
            for( auto lbound = lbounds.rbegin(); lbound != --lbounds.rend(); ++lbound )
            {
                if( **lbound > _bound.limit() && (*lbound)->pAsConstraint() != NULL )
                {
                    Formula* deduction = new Formula( OR );
                    deduction->addSubformula( new Formula( NOT ) );
                    deduction->back()->addSubformula( _bound.pAsConstraint() );
                    deduction->addSubformula( new Formula( NOT ) );
                    deduction->back()->addSubformula( (*lbound)->pAsConstraint() );
                    addDeduction( deduction );
                }
                else
                {
                    break;
                }
            }
        }
        if( _bound.isLowerBound() )
        {
            const BoundSet& ubounds = _bound.variable().upperbounds();
            for( auto ubound = ubounds.begin(); ubound != --ubounds.end(); ++ubound )
            {
                if( **ubound < _bound.limit() && (*ubound)->pAsConstraint() != NULL )
                {
                    Formula* deduction = new Formula( OR );
                    deduction->addSubformula( new Formula( NOT ) );
                    deduction->back()->addSubformula( _bound.pAsConstraint() );
                    deduction->addSubformula( new Formula( NOT ) );
                    deduction->back()->addSubformula( (*ubound)->pAsConstraint() );
                    addDeduction( deduction );
                }
                else
                {
                    break;
                }
            }
        }
    }
    #endif

    /**
     * Initializes the tableau according to all linear constraints, of which this module has been informed.
     */
    void LRAModule::initialize( const Constraint* const _pConstraint )
    {
        CONSTRAINT_LOCK_GUARD
        map<const string, numeric, strCmp> coeffs = _pConstraint->linearAndConstantCoefficients();
        assert( coeffs.size() > 1 );
        map<const string, numeric, strCmp>::iterator currentCoeff = coeffs.begin();
        ex*                                          linearPart   = new ex( _pConstraint->lhs() - currentCoeff->second );
        ++currentCoeff;

        // divide the linear Part and the _pConstraint by the highest coefficient
        numeric highestCoeff = currentCoeff->second;
        --currentCoeff;
        while( currentCoeff != coeffs.end() )
        {
            currentCoeff->second /= highestCoeff;
            ++currentCoeff;
        }
        *linearPart /= highestCoeff;
        if( coeffs.size() == 2 )
        {
            // constraint has one variable
            ex* var = new ex( (*_pConstraint->variables().begin()).second );
            ExVariableMap::iterator basicIter = mOriginalVars.find( var );
            // constraint not found, add new nonbasic variable
            if( basicIter == mOriginalVars.end() )
            {
                Variable* nonBasic = mTableau.newNonbasicVariable( var );
                mOriginalVars.insert( pair<const ex*, Variable*>( var, nonBasic ) );
                setBound( *nonBasic, highestCoeff.is_negative(), -coeffs.begin()->second, _pConstraint );
            }
            else
            {
                delete var;
                Variable* nonBasic = basicIter->second;
                setBound( *nonBasic, highestCoeff.is_negative(), -coeffs.begin()->second, _pConstraint );
            }
            delete linearPart;
        }
        else
        {
            ExVariableMap::iterator slackIter = mSlackVars.find( linearPart );
            if( slackIter == mSlackVars.end() )
            {
                vector< Variable* > nonbasics = vector< Variable* >();
                vector< numeric > numCoeffs = vector< numeric >();
                symtab::const_iterator varIt   = _pConstraint->variables().begin();
                map<const string, numeric, strCmp>::iterator coeffIt = coeffs.begin();
                ++coeffIt;
                while( varIt != _pConstraint->variables().end() )
                {
                    assert( coeffIt != coeffs.end() );
                    ex* var = new ex( varIt->second );
                    ExVariableMap::iterator nonBasicIter = mOriginalVars.find( var );
                    if( mOriginalVars.end() == nonBasicIter )
                    {
                        Variable* nonBasic = mTableau.newNonbasicVariable( var );
                        mOriginalVars.insert( pair<const ex*, Variable*>( var, nonBasic ) );
                        nonbasics.push_back( nonBasic );
                    }
                    else
                    {
                        delete var;
                        nonbasics.push_back( nonBasicIter->second );
                    }
                    numCoeffs.push_back( coeffIt->second );
                    ++varIt;
                    ++coeffIt;
                }

                Variable* slackVar = mTableau.newBasicVariable( linearPart, nonbasics, numCoeffs );

                mSlackVars.insert( pair<const ex*, Variable*>( linearPart, slackVar ) );
                setBound( *slackVar, highestCoeff.is_negative(), -coeffs.begin()->second, _pConstraint );
            }
            else
            {
                delete linearPart;
                Variable* slackVar = slackIter->second;
                setBound( *slackVar, highestCoeff.is_negative(), -coeffs.begin()->second, _pConstraint );
            }
        }
    }

    /**
     * Initializes the tableau according to all linear constraints, of which this module has been informed.
     */
    void LRAModule::initialize()
    {
        if( !mInitialized )
        {
            mInitialized = true;
            for( auto constraint = mLinearConstraints.begin(); constraint != mLinearConstraints.end(); ++constraint )
            {
                initialize( *constraint );
            }
            #ifdef LRA_USE_PIVOTING_STRATEGY
            mTableau.setBlandsRuleStart( mTableau.columns().size() );
            #endif
        }
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
            _out << _init << "   " << (*iter)->smtlibString() << endl;
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
            _out << _init << "   " << (*iter)->smtlibString() << endl;
        }
    }

    /**
     * Prints the original variables with their bounds and the corresponding activation
     * sets (asserted sub-formulas/constraints corresponding to the bounds).
     *
     * @param _out The output stream to print on.
     * @param _init The beginning of each line to print.
     */
    void LRAModule::printOriginalVars( ostream& _out, const string _init ) const
    {
        _out << _init << "Original variables:" << endl;
        for( auto iter = mOriginalVars.begin(); iter != mOriginalVars.end(); ++iter )
        {
            _out << _init << "   " << *iter->first << ":" << endl;
            _out << _init << "          ";
            iter->second->print( _out );
            _out << endl;
            iter->second->printAllBounds( _out, _init + "          " );
        }
    }


    /**
     * Prints the slack/additional variables with their bounds and the corresponding activation
     * sets (asserted sub-formulas/constraints corresponding to the bounds).
     *
     * @param _out The output stream to print on.
     * @param _init The beginning of each line to print.
     */
    void LRAModule::printSlackVars( ostream& _out, const string _init ) const
    {
        _out << _init << "Slack variables:" << endl;
        for( auto iter = mSlackVars.begin(); iter != mSlackVars.end(); ++iter )
        {
            _out << _init << "   " << *iter->first << ":" << endl;
            _out << _init << "          ";
            iter->second->print( _out );
            _out << endl;
            iter->second->printAllBounds( _out, _init + "          " );
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
        for( auto iter = mConstraintToBound.begin(); iter != mConstraintToBound.end(); ++iter )
        {
            _out << _init << "   " << iter->first->smtlibString() << endl;
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
            _out << endl;
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
        exmap rmodel = getRationalModel();
        _out << _init << "Rational model:" << endl;
        for( auto assign = rmodel.begin(); assign != rmodel.end(); ++assign )
        {
            _out << _init;
            _out << setw(10) << assign->first;
            _out << " -> " << assign->second << endl;
        }
    }

}    // namespace smtrat

