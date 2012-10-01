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
#include <algorithm>

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
        mTableau(),
        mLinearConstraints(),
        mNonlinearConstraints(),
        mExistingVars(),
        mConstraintToBound()
    {
        mModuleType = MT_LRAModule;
    }

    /**
     * Destructor:
     */
    LRAModule::~LRAModule()
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
    bool LRAModule::inform( const Constraint* const _constraint )
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
                ConstraintBoundMap::iterator iter = mConstraintToBound.find( constraint );

                if( iter == mConstraintToBound.end() )
                {
                    storeAssumptionsToCheck( *mpManager );
                    cout << **_subformula << endl;
                }
                assert( iter != mConstraintToBound.end() );

                set<const Formula*> originSet = set<const Formula*>();
                originSet.insert( *_subformula );
                activateBound( (*iter).second, originSet );

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
    void LRAModule::removeSubformula( Formula::const_iterator _subformula )
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
            auto originSet = (*iter).second->pOrigins()->begin();
            while(  originSet != (*iter).second->pOrigins()->end() )
            {
                if( originSet->find( *_subformula ) != originSet->end() ) originSet = (*iter).second->pOrigins()->erase( originSet );
                else ++originSet;
            }
            if( (*iter).second->origins().empty() )
            {
                (*iter).second->pVariable()->deactivateBound( (*iter).second );
                if( ((*iter).second->isUpperBound() && (*iter).second->variable().pSupremum()->isInfinite()) || ((*iter).second->isLowerBound() && (*iter).second->variable().pInfimum()->isInfinite()) )
                {
                    if( (*iter).second->variable().isBasic() )
                    {
                        mTableau.decrementBasicActivity( *(*iter).second->pVariable() );
                    }
                    else
                    {
                        mTableau.decrementNonbasicActivity( *(*iter).second->pVariable() );
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
                    for( ; posNewLearnedBound < mTableau.rLearnedBounds().size(); ++posNewLearnedBound )
                    {
                        set< const Formula*> originSet = set< const Formula*>();
                        vector<const Bound*>& bounds = *mTableau.rLearnedBounds()[posNewLearnedBound].second;
                        for( auto bound = bounds.begin(); bound != bounds.end(); ++bound )
                        {
                            originSet.insert( (*bound)->origins().begin()->begin(), (*bound)->origins().begin()->end() );
                        }
                        activateBound( mTableau.rLearnedBounds()[posNewLearnedBound].first, originSet );
                    }
                    ++posNewLearnedBound;
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
    void LRAModule::learnRefinements()
    {
        vector<pair<const Bound*, vector<const Bound* >* > >& lBs = mTableau.rLearnedBounds();
        while( !lBs.empty() )
        {
            Formula* deduction = new Formula( OR );
            for( auto bound = lBs.back().second->begin(); bound != lBs.back().second->end(); ++bound )
            {
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( (*bound)->pAsConstraint() );
            }
            deduction->addSubformula( lBs.back().first->pAsConstraint() );
            addDeduction( deduction );
            vector<set< const Formula* > >& origins = *lBs.back().first->pOrigins();
            auto originSet = origins.begin();
            while( originSet != origins.end() )
            {
                if( originSet->size() != 1 ) originSet = origins.erase( originSet );
                else ++originSet;
            }
            if( origins.empty() ) lBs.back().first->pVariable()->deactivateBound( lBs.back().first );
            vector<const Bound* >* toDelete = lBs.back().second;
            lBs.pop_back();
            delete toDelete;
        }
    }
    #endif

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
    bool LRAModule::activateBound( const Bound* bound, set<const Formula*>& _formulas )
    {
        bound->pOrigins()->push_back( _formulas );
        const Variable& var = bound->variable();
        if( (bound->isUpperBound() && var.pSupremum()->isInfinite()) || (bound->isLowerBound() && var.pInfimum()->isInfinite()) )
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
        if( bound->isUpperBound() )
        {
            if( *var.pInfimum() > bound->limit() )
            {
                set<const Formula*> infsubset = set<const Formula*>();
                infsubset.insert( bound->pOrigins()->begin()->begin(), bound->pOrigins()->begin()->end() );
                infsubset.insert( var.pInfimum()->pOrigins()->back().begin(), var.pInfimum()->pOrigins()->back().end() );
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
        if( bound->isLowerBound() )
        {
            if( *var.pSupremum() < bound->limit() )
            {
                set<const Formula*> infsubset = set<const Formula*>();
                infsubset.insert( bound->pOrigins()->begin()->begin(), bound->pOrigins()->begin()->end() );
                infsubset.insert( var.pSupremum()->pOrigins()->back().begin(), var.pSupremum()->pOrigins()->back().end() );
                mInfeasibleSubsets.push_back( infsubset );
                return false;
            }
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
    void LRAModule::setBound( Variable& var, const Constraint_Relation& rel, bool constraintInverted, const numeric& boundValue, const Constraint* _constraint )
    {
        if( rel == CR_EQ )
        {
            Value* value  = new Value( boundValue );
            pair<const Bound*,pair<const Bound*, const Bound*> > result = var.addEqualBound( value, _constraint );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            findSimpleConflicts( *result.first );
            #endif
            ConstraintBoundPair p = ConstraintBoundPair( _constraint, result.first );
            mConstraintToBound.insert( p );
            #ifdef LRA_SIMPLE_THEORY_PROPAGATION
            if( result.second.first != NULL && result.second.first->pAsConstraint() != NULL )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( _constraint );
                deduction->addSubformula( result.second.first->pAsConstraint() );
                addDeduction( deduction );
            }
            if( result.second.first != NULL && result.second.first->pAsConstraint() != NULL )
            {
                Formula* deduction = new Formula( OR );
                deduction->addSubformula( new Formula( NOT ) );
                deduction->back()->addSubformula( _constraint );
                deduction->addSubformula( result.second.first->pAsConstraint() );
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
        else if( rel == CR_LEQ )
        {
            Value* value = new Value( boundValue );
            pair<const Bound*,pair<const Bound*, const Bound*> > result = constraintInverted ? var.addLowerBound( value, _constraint ) : var.addUpperBound( value, _constraint );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            findSimpleConflicts( *result.first );
            #endif
            ConstraintBoundPair p = ConstraintBoundPair( _constraint, result.first );
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
            pair<const Bound*,pair<const Bound*, const Bound*> > result = constraintInverted ? var.addUpperBound( value, _constraint ) : var.addLowerBound( value, _constraint );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            findSimpleConflicts( *result.first );
            #endif
            ConstraintBoundPair p = ConstraintBoundPair( _constraint, result.first );
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
            pair<const Bound*,pair<const Bound*, const Bound*> > result = constraintInverted ? var.addLowerBound( value, _constraint ) : var.addUpperBound( value, _constraint );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            findSimpleConflicts( *result.first );
            #endif
            ConstraintBoundPair p = ConstraintBoundPair( _constraint, result.first );
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
            pair<const Bound*,pair<const Bound*, const Bound*> > result = constraintInverted ? var.addUpperBound( value, _constraint ) : var.addLowerBound( value, _constraint );
            #ifdef LRA_SIMPLE_CONFLICT_SEARCH
            findSimpleConflicts( *result.first );
            #endif
            ConstraintBoundPair p = ConstraintBoundPair( _constraint, result.first );
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
    void LRAModule::findSimpleConflicts( const Bound& _bound )
    {
        if( _bound.isUpperBound() )
        {
            const BoundSet& lbounds = _bound.variable().lowerbounds();
            for( auto lbound = lbounds.rbegin(); lbound != --lbounds.rend(); ++lbound )
            {
                if( **lbound > _bound.limit() )
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
                if( **ubound < _bound.limit() )
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

