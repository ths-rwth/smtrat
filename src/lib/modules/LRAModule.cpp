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
 * @author name surname <emailadress>
 *
 * @version 2012-04-05
 * Created on April 5th, 2012, 3:22 PM
 */


#include "LRAModule.h"
#include <iostream>

//#define DEBUG_LRA_MODULE
#define LRA_SIMPLE_THEORY_PROPAGATION
#define LRA_ONE_REASON

using namespace std;
using namespace lra;
using namespace GiNaC;

namespace smtrat
{
    /**
     * Constructor
     */
    LRAModule::LRAModule( Manager* const _tsManager, const Formula* const _formula ):
        Module( _tsManager, _formula ),
        mInitialized(),
        mMaxConstraintId( Formula::constraintPool().size() + 1 ),
        mTableau( mpPassedFormula->end() ),
        mLinearConstraints(),
        mNonlinearConstraints(),
        mExistingVars(),
        mConstraintToBound( mMaxConstraintId, NULL ),
        mBoundCandidatesToPass()
    {
        mModuleType = MT_LRAModule;
    }

    /**
     * Destructor:
     */
    LRAModule::~LRAModule()
    {
        while( !mConstraintToBound.empty() )
        {
            vector< const Bound* >* toDelete = mConstraintToBound.back();
            mConstraintToBound.pop_back();
            if( toDelete != NULL ) delete toDelete;
        }
        while( !mExistingVars.empty() )
        {
            const ex* exToDelete = mExistingVars.begin()->first;
            mExistingVars.erase( mExistingVars.begin() );
            delete exToDelete;
        }
    }

    /**
     * Methods:
     */

    /**
     *
     * @param _constraint
     * @return
     */
    bool LRAModule::inform( const Constraint* const _constraint )
    {
        #ifdef DEBUG_LRA_MODULE
        cout << "inform about " << *_constraint << endl;
        #endif
        if( _constraint->isConsistent() == 2 && _constraint->isLinear() )
        {
            mLinearConstraints.insert( _constraint );
            if( _constraint->id() > mMaxConstraintId ) mMaxConstraintId = _constraint->id();
        }
        return true;
    }

    /**
     *
     * @param _formula
     * @return
     */
    bool LRAModule::assertSubformula( Formula::const_iterator _subformula )
    {
        assert( (*_subformula)->getType() == REALCONSTRAINT );
        assert( (*_subformula)->constraint().relation() != CR_NEQ );
        #ifdef DEBUG_LRA_MODULE
        cout << "assert " << (*_subformula)->constraint() << endl;
        #endif
        if( !mInitialized ) initialize();
        Module::assertSubformula( _subformula );

        const Constraint* constraint  = (*_subformula)->pConstraint();
        int               consistency = constraint->isConsistent();
        if( consistency == 2 )
        {
            if( constraint->isLinear() )
            {
                vector< const Bound* >& bounds = *mConstraintToBound[constraint->id()];
                set<const Formula*> originSet = set<const Formula*>();
                originSet.insert( *_subformula );
                activateBound( *bounds.begin(), originSet );

                assert( mInfeasibleSubsets.empty() || !mInfeasibleSubsets.begin()->empty() );
                return mInfeasibleSubsets.empty() || !mNonlinearConstraints.empty();
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
            return false;
        }
        else
        {
            return true;
        }
    }

    /**
     *
     * @param _subformula
     */
    void LRAModule::removeSubformula( Formula::const_iterator _subformula )
    {
        #ifdef DEBUG_LRA_MODULE
        cout << "remove " << (*_subformula)->constraint() << endl;
        #endif
        // Remove the mapping of the constraint to the sub-formula in the received formula
        const Constraint* constraint = (*_subformula)->pConstraint();
        if( constraint->isConsistent() == 2 )
        {
            if( constraint->isLinear() )
            {
                // Deactivate the bounds regarding the given constraint
                vector< const Bound* >& bounds = *mConstraintToBound[constraint->id()];
                auto bound = bounds.begin();
                while( bound != bounds.end() )
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
                    if( (*bound)->origins().empty() && (*bound)->deduced() )
                    {
                        bound = bounds.erase( bound );
                    }
                    else
                    {
                        ++bound;
                    }
                }
            }
            else
            {
                mNonlinearConstraints.erase( constraint );
            }
        }
        Module::removeSubformula( _subformula );
    }

    /**
     *
     * @return
     */
    Answer LRAModule::isConsistent()
    {
        #ifdef DEBUG_LRA_MODULE
        cout << "check for consistency" << endl;
        #endif
        if( !mInfeasibleSubsets.empty() )
        {
            return False;
        }
        unsigned posNewLearnedBound = 0;
        for( ; ; )
        {
            #ifdef DEBUG_LRA_MODULE
            cout << endl;
            mTableau.printVariables( cout, "    " );
            cout << endl;
            mTableau.print( cout, 15, "    " );
            cout << endl;
            #endif

            pair<EntryID,bool> pivotingElement = mTableau.nextPivotingElement();

            #ifdef DEBUG_LRA_MODULE
            cout << "    Next pivoting element: ";
            mTableau.printEntry( cout, pivotingElement.first );
            cout << (pivotingElement.second ? "(True)" : "(False)");
            cout << " [" << pivotingElement.first << "]" << endl;
            #endif

            if( pivotingElement.second )
            {
                if( pivotingElement.first == 0 )
                {
                    #ifdef DEBUG_LRA_MODULE
                    cout << "True" << endl;
                    #endif
                    if( checkAssignmentForNonlinearConstraint() )
                    {
                        learnRefinements();
                        return True;
                    }
                    else
                    {
                        adaptPassedFormula();
                        Answer a = runBackends();
                        if( a == False )
                        {
                            getInfeasibleSubsets();
                        }
                        learnRefinements();
                        return a;
                    }
                }
                else
                {
                    mTableau.pivot( pivotingElement.first );
                    while( posNewLearnedBound < mTableau.rLearnedBounds().size() )
                    {
                        set< const Formula*> originSet = set< const Formula*>();
                        vector<const Bound*>& bounds = *mTableau.rLearnedBounds()[posNewLearnedBound].premise;
                        for( auto bound = bounds.begin(); bound != bounds.end(); ++bound )
                        {
                            assert( !(*bound)->origins().empty() );
                            originSet.insert( (*bound)->origins().begin()->begin(), (*bound)->origins().begin()->end() );
                            for( auto origin = (*bound)->origins().begin()->begin(); origin != (*bound)->origins().begin()->end(); ++origin )
                            {
                                const Constraint* constraint = (*origin)->pConstraint();
                                if( constraint != NULL )
                                {
                                    mConstraintToBound[constraint->id()]->push_back( mTableau.rLearnedBounds()[posNewLearnedBound].nextWeakerBound );
                                    mConstraintToBound[constraint->id()]->push_back( mTableau.rLearnedBounds()[posNewLearnedBound].newBound );
                                }
                            }
                        }
                        activateBound( mTableau.rLearnedBounds()[posNewLearnedBound].nextWeakerBound, originSet );
                        activateBound( mTableau.rLearnedBounds()[posNewLearnedBound].newBound, originSet );
                        ++posNewLearnedBound;
                    }
                    if( !mInfeasibleSubsets.empty() )
                    {
                        learnRefinements();
                        return False;
                    }
                }
            }
            else
            {
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
                learnRefinements();
                #ifdef DEBUG_LRA_MODULE
                cout << "False" << endl;
                #endif
                return False;
            }
        }
        assert( false );
        learnRefinements();
        return True;
    }

    #ifdef LRA_REFINEMENT
    /**
     *
     */
    void LRAModule::learnRefinements()
    {
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
     *
     * @return
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
                removeSubformulaFromPassedFormula( bound.pInfo()->position );
                bound.pInfo()->position = mpPassedFormula->end();
                bound.pInfo()->updated = 0;
            }
            mBoundCandidatesToPass.pop_back();
        }
    }

    /**
     *
     * @return
     */
    bool LRAModule::checkAssignmentForNonlinearConstraint() const
    {
        if( mNonlinearConstraints.empty() )
        {
            return true;
        }
        else
        {
            // TODO: check whether the found satisfying assignment is by coincidence a
            // satisfying assignment of the non linear constraints
            return false;
        }
    }

    /**
     *
     * @param _var
     * @param bound
     * @return
     */
    bool LRAModule::activateBound( const Bound* _bound, set<const Formula*>& _formulas )
    {
        _bound->pOrigins()->push_back( _formulas );
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
            if( *var.pInfimum() > _bound->limit() )
            {
                set<const Formula*> infsubset = set<const Formula*>();
                infsubset.insert( _bound->pOrigins()->begin()->begin(), _bound->pOrigins()->begin()->end() );
                infsubset.insert( var.pInfimum()->pOrigins()->back().begin(), var.pInfimum()->pOrigins()->back().end() );
                mInfeasibleSubsets.push_back( infsubset );
                return false;
            }
            if( *var.pSupremum() > *_bound )
            {
                if( !var.pSupremum()->isInfinite() )
                {
                    mBoundCandidatesToPass.push_back( var.pSupremum() );
                }
                mBoundCandidatesToPass.push_back( _bound );
                _bound->pVariable()->setSupremum( _bound );

                if( !var.isBasic() && (*var.pSupremum() < var.assignment()) )
                {
                    mTableau.updateBasicAssignments( var.position(), Value( (*var.pSupremum()).limit() - var.assignment() ) );
                    _bound->pVariable()->rAssignment() = (*var.pSupremum()).limit();
                }
            }
        }
        if( _bound->isLowerBound() )
        {
            if( *var.pSupremum() < _bound->limit() )
            {
                set<const Formula*> infsubset = set<const Formula*>();
                infsubset.insert( _bound->pOrigins()->begin()->begin(), _bound->pOrigins()->begin()->end() );
                infsubset.insert( var.pSupremum()->pOrigins()->back().begin(), var.pSupremum()->pOrigins()->back().end() );
                mInfeasibleSubsets.push_back( infsubset );
                return false;
            }
            if( *var.pInfimum() < *_bound )
            {
                if( !var.pInfimum()->isInfinite() )
                {
                    mBoundCandidatesToPass.push_back( var.pInfimum() );
                }
                mBoundCandidatesToPass.push_back( _bound );
                _bound->pVariable()->setInfimum( _bound );

                if( !var.isBasic() && (*var.pInfimum() > var.assignment()) )
                {
                    mTableau.updateBasicAssignments( var.position(), Value( (*var.pInfimum()).limit() - var.assignment() ) );
                    _bound->pVariable()->rAssignment() = (*var.pInfimum()).limit();
                }
            }
        }
        return true;
    }

    /**
     *
     * @param var
     * @param rel
     * @param negativ
     * @param boundValue
     * @param constr
     */
    void LRAModule::setBound( Variable& var, const Constraint_Relation& rel, bool constraintInverted, const numeric& boundValue, const Constraint* _constraint )
    {
        assert( _constraint->id() < mMaxConstraintId );
        if( rel == CR_EQ )
        {
            // TODO: Take value from an allocator to assure the values are located close to each other in the memory.
            Value* value  = new Value( boundValue );
            pair<const Bound* ,pair<const Bound*, const Bound*> > result = var.addEqualBound( value, mpPassedFormula->end(), _constraint );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            findSimpleConflicts( *result.first );
            #endif
            vector< const Bound* >* boundVector = new vector< const Bound* >();
            boundVector->push_back( result.first );
            mConstraintToBound[_constraint->id()] = boundVector;
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
        else if( rel == CR_LEQ )
        {
            Value* value = new Value( boundValue );
            pair<const Bound*,pair<const Bound*, const Bound*> > result = constraintInverted ? var.addLowerBound( value, mpPassedFormula->end(), _constraint ) : var.addUpperBound( value, mpPassedFormula->end(), _constraint );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            findSimpleConflicts( *result.first );
            #endif
            vector< const Bound* >* boundVector = new vector< const Bound* >();
            boundVector->push_back( result.first );
            mConstraintToBound[_constraint->id()] = boundVector;
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
        else if( rel == CR_GEQ )
        {
            Value* value = new Value( boundValue );
            pair<const Bound*,pair<const Bound*, const Bound*> > result = constraintInverted ? var.addUpperBound( value, mpPassedFormula->end(), _constraint ) : var.addLowerBound( value, mpPassedFormula->end(), _constraint );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            findSimpleConflicts( *result.first );
            #endif
            vector< const Bound* >* boundVector = new vector< const Bound* >();
            boundVector->push_back( result.first );
            mConstraintToBound[_constraint->id()] = boundVector;
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
        else if( rel == CR_LESS )
        {
            Value* value = new Value( boundValue, (constraintInverted ? 1 : -1) );
            pair<const Bound*,pair<const Bound*, const Bound*> > result = constraintInverted ? var.addLowerBound( value, mpPassedFormula->end(), _constraint ) : var.addUpperBound( value, mpPassedFormula->end(), _constraint );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            findSimpleConflicts( *result.first );
            #endif
            vector< const Bound* >* boundVector = new vector< const Bound* >();
            boundVector->push_back( result.first );
            mConstraintToBound[_constraint->id()] = boundVector;
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
        else if( rel == CR_GREATER )
        {
            Value* value = new Value( boundValue, (constraintInverted ? -1 : 1) );
            pair<const Bound*,pair<const Bound*, const Bound*> > result = constraintInverted ? var.addUpperBound( value, mpPassedFormula->end(), _constraint ) : var.addLowerBound( value, mpPassedFormula->end(), _constraint );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            findSimpleConflicts( *result.first );
            #endif
            vector< const Bound* >* boundVector = new vector< const Bound* >();
            boundVector->push_back( result.first );
            mConstraintToBound[_constraint->id()] = boundVector;
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
    }

    #ifdef LRA_SIMPLE_CONFLICT_SEARCH
    /**
     *
     * @param _bound
     */
    void LRAModule::findSimpleConflicts( const Bound& _bound )
    {
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
     *
     */
    void LRAModule::initialize()
    {
        mInitialized = true;
        //TODO: sort the constraints as a first kind of a pivoting strategy
        for( auto constraint = mLinearConstraints.begin(); constraint != mLinearConstraints.end(); ++constraint )
        {
            map<const string, numeric, strCmp> coeffs = (*constraint)->linearAndConstantCoefficients();
            assert( coeffs.size() > 1 );
            map<const string, numeric, strCmp>::iterator currentCoeff = coeffs.begin();
            ex*                                          linearPart   = new ex( (*constraint)->lhs() - currentCoeff->second );
            ++currentCoeff;

            // divide the linear Part and the constraint by the highest coefficient
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
                ex* var = new ex( (*(*constraint)->variables().begin()).second );
                ExVariableMap::iterator basicIter = mExistingVars.find( var );
                // constraint not found, add new nonbasic variable
                if( basicIter == mExistingVars.end() )
                {
                    Variable* nonBasic = mTableau.newNonbasicVariable( var );
                    mExistingVars.insert( pair<const ex*, Variable*>( var, nonBasic ) );
                    setBound( *nonBasic, (*constraint)->relation(), highestCoeff.is_negative(), -coeffs.begin()->second, *constraint );
                }
                else
                {
                    delete var;
                    Variable* nonBasic = basicIter->second;
                    setBound( *nonBasic, (*constraint)->relation(), highestCoeff.is_negative(), -coeffs.begin()->second, *constraint );
                }

            }
            else
            {
                ExVariableMap::iterator slackIter = mExistingVars.find( linearPart );
                if( slackIter == mExistingVars.end() )
                {
                    vector< Variable* > nonbasics = vector< Variable* >();
                    vector< numeric > numCoeffs = vector< numeric >();
                    symtab::const_iterator varIt   = (*constraint)->variables().begin();
                    map<const string, numeric, strCmp>::iterator coeffIt = coeffs.begin();
                    ++coeffIt;
                    while( varIt != (*constraint)->variables().end() )
                    {
                        assert( coeffIt != coeffs.end() );
                        ex* var = new ex( varIt->second );
                        ExVariableMap::iterator nonBasicIter = mExistingVars.find( var );
                        if( mExistingVars.end() == nonBasicIter )
                        {
                            Variable* nonBasic = mTableau.newNonbasicVariable( var );
                            mExistingVars.insert( pair<const ex*, Variable*>( var, nonBasic ) );
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

                    mExistingVars.insert( pair<const ex*, Variable*>( linearPart, slackVar ) );
                    setBound( *slackVar, (*constraint)->relation(), highestCoeff.is_negative(), -coeffs.begin()->second, *constraint );
                }
                else
                {
                    delete linearPart;
                    Variable* slackVar = slackIter->second;
                    setBound( *slackVar, (*constraint)->relation(), highestCoeff.is_negative(), -coeffs.begin()->second, *constraint );
                }
            }
        }
        #ifdef LRA_USE_PIVOTING_STRATEGY
        mTableau.setBlandsRuleStart( mTableau.columns().size() );
        #endif
    }

}    // namespace smtrat

