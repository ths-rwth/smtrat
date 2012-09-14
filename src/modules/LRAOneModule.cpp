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
 * File:   LRAOneModule.cpp
 * @author name surname <emailadress>
 *
 * @version 2012-04-05
 * Created on April 5th, 2012, 3:22 PM
 */


#include "LRAOneModule.h"
#include "LRATwoModule/Bound.h"
#include <iostream>
#include <algorithm>

#define DEBUG_LRA_MODULE
#define LRA_SIMPLE_THEORY_PROPAGATION
#define LRA_ONE_REASON

using namespace std;
using namespace lraone;
using namespace GiNaC;

namespace smtrat
{
    /**
     * Constructor
     */
    LRAOneModule::LRAOneModule( Manager* const _tsManager, const Formula* const _formula ):
        Module( _tsManager, _formula ),
        mInitialized(),
        mTableau(),
        mLinearConstraints(),
        mNonlinearConstraints(),
        mExistingVars(),
        mConstraintToBound()
    {
        mModuleType = MT_LRAOneModule;
    }

    /**
     * Destructor:
     */
    LRAOneModule::~LRAOneModule()
    {
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
    bool LRAOneModule::inform( const Constraint* const _constraint )
    {
        #ifdef DEBUG_LRA_MODULE
        cout << "inform about " << *_constraint << endl;
        #endif
        if( _constraint->isConsistent() == 2 && _constraint->isLinear() )
        {
            mLinearConstraints.insert( _constraint );
        }
        return true;
    }

    /**
     *
     * @param _formula
     * @return
     */
    bool LRAOneModule::assertSubformula( Formula::const_iterator _subformula )
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
                ConstraintBoundMap::iterator iter = mConstraintToBound.find( constraint );

                assert( iter != mConstraintToBound.end() );

                vector<const lraone::Bound*> boundL = (*iter).second;

                //iterate through bound vector, necessary for equal
                for( vector<const lraone::Bound*>::const_iterator bIter = boundL.begin(); bIter != boundL.end(); ++bIter )
                {
                    activateBound( *bIter, *_subformula );
                }
                assert( mInfeasibleSubsets.empty() || !mInfeasibleSubsets.begin()->empty() );
                return mInfeasibleSubsets.empty() || !mNonlinearConstraints.empty();
            }
            else
            {
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
    void LRAOneModule::removeSubformula( Formula::const_iterator _subformula )
    {
        #ifdef DEBUG_LRA_MODULE
        cout << "remove " << (*_subformula)->constraint() << endl;
        #endif

        // Remove the mapping of the constraint to the sub-formula in the received formula
        const Constraint* constraint = (*_subformula)->pConstraint();
        if( constraint->isConsistent() == 2 )
        {
            // Deactivate the bounds regarding the given constraint
            ConstraintBoundMap::iterator iter = mConstraintToBound.find( constraint );
            assert( iter != mConstraintToBound.end() );
            vector<const lraone::Bound*> boundL = (*iter).second;
            for( vector<const lraone::Bound*>::const_iterator bIter = boundL.begin(); bIter != boundL.end(); ++bIter )
            {
                (*bIter)->pOrigins()->erase( *_subformula );
                (*bIter)->pVariable()->deactivateBound( *bIter );
                if( ((*bIter)->isUpper() && (*bIter)->variable().pSupremum()->isInfinite()) || (!(*bIter)->isUpper() && (*bIter)->variable().pInfimum()->isInfinite()) )
                {
                    if( (*bIter)->variable().isBasic() )
                    {
                        mTableau.decrementBasicActivity( *(*bIter)->pVariable() );
                    }
                    else
                    {
                        mTableau.decrementNonbasicActivity( *(*bIter)->pVariable() );
                    }
                }
            }
        }
        Module::removeSubformula( _subformula );
    }

    /**
     *
     * @return
     */
    Answer LRAOneModule::isConsistent()
    {
        #ifdef DEBUG_LRA_MODULE
        cout << "check for consistency" << endl;
        #endif
        if( !mInfeasibleSubsets.empty() )
        {
            return False;
        }
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
                        return True;
                    }
                    else
                    {
                        Answer a = runBackends();
                        if( a == False )
                        {
                            getInfeasibleSubsets();
                        }
                        return a;
                    }
                }
                else
                {
                    mTableau.pivot( pivotingElement.first );
                    #ifdef LRA_REFINEMENT
                    vector<pair<const lraone::Bound*, vector<Formula* > > >& lBs = mTableau.learnedBounds();
                    while( !lBs.empty() )
                    {
                        for( auto deduction = lBs.back().second.begin(); deduction != lBs.back().second.end(); ++deduction )
                        {
                            addDeduction( *deduction );
                        }
                        #ifdef LRA_PROPAGATE_NEW_CONSTRAINTS
                        vector<const lraone::Bound*> bounds = vector<const lraone::Bound*>();
                        bounds.push_back( lBs.back().first );
                        ConstraintBoundPair p = ConstraintBoundPair( lBs.back().first->pAsConstraint(), bounds );
                        mConstraintToBound.insert( p );
                        #endif
                        lBs.back().first->pOrigins()->clear();
                        lBs.pop_back();
                    }
                    #endif
                }
            }
            else
            {
                #ifdef LRA_ONE_REASON
                vector< const lraone::Bound* > conflict = mTableau.getConflict( pivotingElement.first );
                set< const Formula* > infSubSet = set< const Formula* >();
                for( auto bound = conflict.begin(); bound != conflict.end(); ++bound )
                {
                    assert( (*bound)->isActive() );
                    infSubSet.insert( *(*bound)->pOrigins()->begin() );
                }
                mInfeasibleSubsets.push_back( infSubSet );
                #else
                vector< set< const lraone::Bound* > > conflictingBounds = mTableau.getConflictsFrom( pivotingElement.first );
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
                #ifdef DEBUG_LRA_MODULE
                cout << "False" << endl;
                #endif
                return False;
            }
        }
        assert( false );
        return True;
    }

    bool LRAOneModule::checkAssignmentForNonlinearConstraint() const
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
    bool LRAOneModule::activateBound( const lraone::Bound* bound, const Formula* _formula )
    {
        bound->pOrigins()->insert( _formula );
        const Variable& var = bound->variable();
        if( (bound->isUpper() && var.pSupremum()->isInfinite()) || (!bound->isUpper() && var.pInfimum()->isInfinite()) )
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
        bool isUpper = bound->isUpper();
        if( isUpper )
        {
            if( *var.pInfimum() > *bound )
            {
                set<const Formula*> infsubset = set<const Formula*>();
                infsubset.insert( *bound->pOrigins()->begin() );
                infsubset.insert( *var.pInfimum()->pOrigins()->begin() );
                mInfeasibleSubsets.push_back( infsubset );
                return false;
            }
            if( *var.pSupremum() > *bound )
            {
                bound->pVariable()->setSupremum( bound );

                if( !var.isBasic() && (*var.pSupremum() < var.assignment()) )
                {
                    mTableau.updateBasicAssignments( var.position(), Value( (*var.pSupremum()).limit() - var.assignment() ) );
                    bound->pVariable()->rAssignment() = (*var.pSupremum()).limit();
                }
            }
        }
        else
        {
            if( *var.pSupremum() < *bound )
            {
                set<const Formula*> infsubset = set<const Formula*>();
                infsubset.insert( *bound->pOrigins()->begin() );
                infsubset.insert( *var.pSupremum()->pOrigins()->begin() );
                mInfeasibleSubsets.push_back( infsubset );
                return false;
            }
            //check if the new lower bound is bigger
            if( *var.pInfimum() < *bound )
            {
                bound->pVariable()->setInfimum( bound );

                if( !var.isBasic() && (*var.pInfimum() > var.assignment()) )
                {
                    mTableau.updateBasicAssignments( var.position(), Value( (*var.pInfimum()).limit() - var.assignment() ) );
                    bound->pVariable()->rAssignment() = (*var.pInfimum()).limit();
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
    void LRAOneModule::setBound( Variable& var, const Constraint_Relation& rel, bool constraintInverted, const numeric& boundValue, const Constraint* _constraint )
    {
        if( rel == CR_EQ )
        {
            Value* valueA  = new Value( boundValue );
            Value* valueB  = new Value( boundValue );
            const Constraint* constraintA = Formula::newConstraint( _constraint->lhs(), CR_LEQ );
            const Constraint* constraintB = Formula::newConstraint( _constraint->lhs(), CR_GEQ );
            pair<const lraone::Bound*,pair<const lraone::Bound*, const lraone::Bound*> > resultA = var.addUpperBound( valueA, constraintA );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            findSimpleConflicts( *resultA.first );
            #endif
            pair<const lraone::Bound*,pair<const lraone::Bound*, const lraone::Bound*> > resultB = var.addLowerBound( valueB, constraintB );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            findSimpleConflicts( *resultB.first );
            #endif
            vector<const lraone::Bound*> eqBounds = vector<const lraone::Bound*>();
            eqBounds.push_back( resultA.first );
            eqBounds.push_back( resultB.first );
            ConstraintBoundPair p = ConstraintBoundPair( _constraint, eqBounds );
            mConstraintToBound.insert( p );
            #ifdef LRA_SIMPLE_THEORY_PROPAGATION
            if( resultA.second.first != NULL && resultA.second.first->pAsConstraint() != NULL )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( resultA.second.first->pAsConstraint() );
                deduction->addSubformula( constraintA );
                addDeduction( deduction );
            }
            if( resultB.second.first != NULL && resultB.second.first->pAsConstraint() != NULL )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( resultB.second.first->pAsConstraint() );
                deduction->addSubformula( constraintB );
                addDeduction( deduction );
            }
            if( resultA.second.second != NULL && resultA.second.second->pAsConstraint() != NULL )
            {
                Formula* deductionA = new Formula( OR );
                deductionA->addSubformula( new Formula( NOT ) );
                deductionA->back()->addSubformula( _constraint );
                deductionA->addSubformula( resultA.second.second->pAsConstraint() );
                addDeduction( deductionA );
                Formula* deductionB = new Formula( OR );
                deductionB->addSubformula( new Formula( NOT ) );
                deductionB->back()->addSubformula( constraintA );
                deductionB->addSubformula( resultA.second.second->pAsConstraint() );
                addDeduction( deductionB );
            }
            if( resultB.second.second != NULL && resultB.second.second->pAsConstraint() != NULL )
            {
                Formula* deductionA = new Formula( OR );
                deductionA->addSubformula( new Formula( NOT ) );
                deductionA->back()->addSubformula( _constraint );
                deductionA->addSubformula( resultB.second.second->pAsConstraint() );
                addDeduction( deductionA );
                Formula* deductionB = new Formula( OR );
                deductionB->addSubformula( new Formula( NOT ) );
                deductionB->back()->addSubformula( constraintB );
                deductionB->addSubformula( resultB.second.second->pAsConstraint() );
                addDeduction( deductionB );
            }
            #endif
        }
        else if( rel == CR_LEQ )
        {
            Value* value = new Value( boundValue );
            pair<const lraone::Bound*,pair<const lraone::Bound*, const lraone::Bound*> > result = constraintInverted ? var.addLowerBound( value, _constraint ) : var.addUpperBound( value, _constraint );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            findSimpleConflicts( *result.first );
            #endif
            vector<const lraone::Bound*> vecto = vector<const lraone::Bound*>();
            vecto.push_back( result.first );
            ConstraintBoundPair p = ConstraintBoundPair( _constraint, vecto );
            mConstraintToBound.insert( p );
            #ifdef LRA_SIMPLE_THEORY_PROPAGATION
            if( result.second.first != NULL && result.second.first->pAsConstraint() != NULL )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( result.second.first->pAsConstraint() );
                deduction->addSubformula( _constraint );
                addDeduction( deduction );
            }
            if( result.second.second != NULL && result.second.second->pAsConstraint() != NULL )
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
            pair<const lraone::Bound*,pair<const lraone::Bound*, const lraone::Bound*> > result = constraintInverted ? var.addUpperBound( value, _constraint ) : var.addLowerBound( value, _constraint );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            findSimpleConflicts( *result.first );
            #endif
            vector<const lraone::Bound*> vecto = vector<const lraone::Bound*>();
            vecto.push_back( result.first );
            ConstraintBoundPair p = ConstraintBoundPair( _constraint, vecto );
            mConstraintToBound.insert( p );
            #ifdef LRA_SIMPLE_THEORY_PROPAGATION
            if( result.second.first != NULL && result.second.first->pAsConstraint() != NULL )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( result.second.first->pAsConstraint() );
                deduction->addSubformula( _constraint );
                addDeduction( deduction );
            }
            if( result.second.second != NULL && result.second.second->pAsConstraint() != NULL )
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
            pair<const lraone::Bound*,pair<const lraone::Bound*, const lraone::Bound*> > result = constraintInverted ? var.addLowerBound( value, _constraint ) : var.addUpperBound( value, _constraint );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            findSimpleConflicts( *result.first );
            #endif
            vector<const lraone::Bound*> vecto = vector<const lraone::Bound*>();
            vecto.push_back( result.first );
            ConstraintBoundPair p = ConstraintBoundPair( _constraint, vecto );
            mConstraintToBound.insert( p );
            #ifdef LRA_SIMPLE_THEORY_PROPAGATION
            if( result.second.first != NULL && result.second.first->pAsConstraint() != NULL )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( result.second.first->pAsConstraint() );
                deduction->addSubformula( _constraint );
                addDeduction( deduction );
            }
            if( result.second.second != NULL && result.second.second->pAsConstraint() != NULL )
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
            pair<const lraone::Bound*,pair<const lraone::Bound*, const lraone::Bound*> > result = constraintInverted ? var.addUpperBound( value, _constraint ) : var.addLowerBound( value, _constraint );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            findSimpleConflicts( *result.first );
            #endif
            vector<const lraone::Bound*> vecto = vector<const lraone::Bound*>();
            vecto.push_back( result.first );
            ConstraintBoundPair p = ConstraintBoundPair( _constraint, vecto );
            mConstraintToBound.insert( p );
            #ifdef LRA_SIMPLE_THEORY_PROPAGATION
            if( result.second.first != NULL && result.second.first->pAsConstraint() != NULL )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( result.second.first->pAsConstraint() );
                deduction->addSubformula( _constraint );
                addDeduction( deduction );
            }
            if( result.second.second != NULL && result.second.second->pAsConstraint() != NULL )
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
    void LRAOneModule::findSimpleConflicts( const lraone::Bound& _bound )
    {
        if( _bound.isUpper() )
        {
            for( auto lbound = _bound.variable().lowerbounds().rbegin(); lbound != --_bound.variable().lowerbounds().rend(); ++lbound )
            {
                if( **lbound > _bound )
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
        else
        {
            for( auto ubound = _bound.variable().upperbounds().begin(); ubound != --_bound.variable().upperbounds().end(); ++ubound )
            {
                if( **ubound < _bound )
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
    void LRAOneModule::initialize()
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
                currentCoeff->second = currentCoeff->second / highestCoeff;
                ++currentCoeff;
            }
            *linearPart = *linearPart / highestCoeff;
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
        mTableau.setBlandsRuleStart( mTableau.columns().size() * 4 );
        #endif
    }



    /**
     *
     * @return
     */
    bool LRAOneModule::allPassedconstraintsAreConsidered() const
    {
        for( auto constraint = rReceivedFormula().begin(); constraint != rReceivedFormula().end(); ++constraint )
        {
            bool constraintConsidered = false;
            for( auto column = mTableau.columns().begin(); column != mTableau.columns().end(); ++column )
            {
                for( auto bound = column->mName->upperbounds().begin(); bound != column->mName->upperbounds().end(); ++bound )
                {
                    if( (*bound)->origins().find( *constraint ) != (*bound)->origins().end() )
                    {
                        constraintConsidered = true;
                        break;
                    }
                }
                if( !constraintConsidered )
                {
                    for( auto bound = column->mName->lowerbounds().begin(); bound != column->mName->lowerbounds().end(); ++bound )
                    {
                        if( (*bound)->origins().find( *constraint ) != (*bound)->origins().end() )
                        {
                            constraintConsidered = true;
                            break;
                        }
                    }
                }
                if( constraintConsidered ) break;
            }
            if( !constraintConsidered )
            {
                for( auto row = mTableau.rows().begin(); row != mTableau.rows().end(); ++row )
                {
                    for( auto bound = row->mName->upperbounds().begin(); bound != row->mName->upperbounds().end(); ++bound )
                    {
                        if( (*bound)->origins().find( *constraint ) != (*bound)->origins().end() )
                        {
                            constraintConsidered = true;
                            break;
                        }
                    }
                    if( !constraintConsidered )
                    {
                        for( auto bound = row->mName->lowerbounds().begin(); bound != row->mName->lowerbounds().end(); ++bound )
                        {
                            if( (*bound)->origins().find( *constraint ) != (*bound)->origins().end() )
                            {
                                constraintConsidered = true;
                                break;
                            }
                        }
                    }
                    if( constraintConsidered ) break;
                }
            }
            if( !constraintConsidered ) return false;
        }
        return true;
    }
}    // namespace smtrat

