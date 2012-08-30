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
#include <iostream>
#include <algorithm>

#define DEBUG_LRA_MODULE

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
        mTableau(),
        mLinearConstraints(),
        mNonlinearConstraints(),
        mInitialized( false ),
        mExistingVars(),
        mBoundToConstraint(),
        mConstraintToFormula(),
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
        if( _constraint->isConsistent() == 2 )
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
        #ifdef DEBUG_LRA_MODULE
        cout << "assert " << (*_subformula)->constraint() << endl;
        #endif
        Module::assertSubformula( _subformula );
        if( !mInitialized )
        {
            initialize();
        }

        const Constraint* constraint  = (*_subformula)->pConstraint();
        int               consistency = constraint->isConsistent();
        if( consistency == 2 )
        {
            if( constraint->isLinear() )
            {
                pair<const Constraint*, const Formula* const > cFpair = pair<const Constraint*, const Formula* const >( constraint, *_subformula );
                mConstraintToFormula.insert( cFpair );
                ConstraintBoundMap::iterator iter = mConstraintToBound.find( constraint );

                assert( iter != mConstraintToBound.end() );

                vector<const Bound*> boundL = (*iter).second;

                //iterate through bound vector, necessary for equal
                for( vector<const Bound*>::const_iterator bIter = boundL.begin(); bIter != boundL.end(); ++bIter )
                {
                    if( !activateBound( *(*bIter)->pVariable(), *bIter ) )
                    {
                        // Bound creates directly a conflict
                        const Variable* var = (*bIter)->pVariable();
                        if( (*bIter)->isUpper() )
                        {
                            BoundActivityMap::const_iterator bound = var->lowerbounds().begin();
                            while( bound != var->lowerbounds().end() )
                            {
                                if( *(bound->first) > **bIter )
                                {
                                    if( bound->second > 0 )
                                    {
                                        set<const Formula*> infsubset = set<const Formula*>();
                                        infsubset.insert( *_subformula );
                                        infsubset.insert( getSubformula( bound->first ) );
                                        mInfeasibleSubsets.push_back( infsubset );
                                    }
                                }
                                else
                                {
                                    break;
                                }
                                ++bound;
                            }
                        }
                        else
                        {
                            BoundActivityMap::const_iterator bound = var->upperbounds().begin();
                            while( bound != var->upperbounds().end() )
                            {
                                if( *(bound->first) < **bIter )
                                {
                                    if( bound->second > 0 )
                                    {
                                        set<const Formula*> infsubset = set<const Formula*>();
                                        infsubset.insert( *_subformula );
                                        infsubset.insert( getSubformula( bound->first ) );
                                        mInfeasibleSubsets.push_back( infsubset );
                                    }
                                }
                                else
                                {
                                    break;
                                }
                                ++bound;
                            }
                        }
                    }
                }
                return mInfeasibleSubsets.empty() || !mNonlinearConstraints.empty();
            }
            else
            {
                mNonlinearConstraints.insert( constraint );
                return true;
            }
        }
        else
        {
            return (consistency == 1);
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
        mConstraintToFormula.erase( constraint );
        // Deactivate the bounds regarding the given constraint
        ConstraintBoundMap::iterator iter = mConstraintToBound.find( constraint );
        assert( iter != mConstraintToBound.end() );
        vector<const Bound*> boundL = (*iter).second;
        for( vector<const Bound*>::const_iterator bIter = boundL.begin(); bIter != boundL.end(); ++bIter )
        {
            (*bIter)->pVariable()->deactivateBound( *bIter );
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
        if( !mInfeasibleSubsets.empty() ) return False;
        while( true )
        {
            #ifdef DEBUG_LRA_MODULE
            cout << endl;
            mTableau.printHeap();
            cout << endl;
            mTableau.printVariables();
            cout << endl;
            mTableau.print();
            cout << endl;
            #endif

            pair<EntryID,bool> pivotingElement = mTableau.nextPivotingElement();

            #ifdef DEBUG_LRA_MODULE
            cout << "Next pivoting element: ";
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
                    return (checkAssignmentForNonlinearConstraint() ? True : Unknown );
                }
                else
                {
                    mTableau.pivot( pivotingElement.first );
                }
            }
            else
            {
                vector< set< const Bound* > > conflictingBounds = mTableau.getConflicts( pivotingElement.first );
                for( auto conflict = conflictingBounds.begin(); conflict != conflictingBounds.end(); ++conflict )
                {
                    set< const Formula* > infSubSet = set< const Formula* >();
                    for( auto bound = conflict->begin(); bound != conflict->end(); ++bound )
                    {
                        infSubSet.insert( getSubformula( *bound ) );
                    }
                    mInfeasibleSubsets.push_back( infSubSet );
                }
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
     * @param _bound
     * @return
     */
    const Formula* LRAOneModule::getSubformula( const lraone::Bound* _bound ) const
    {
        BoundConstraintMap::const_iterator it = mBoundToConstraint.find( _bound );
        assert( it != mBoundToConstraint.end() );
        const Constraint* constraint = (*it).second;
        ConstraintFormulaMap::const_iterator consToForm = mConstraintToFormula.find( constraint );
        assert( consToForm != mConstraintToFormula.end() );
        return consToForm->second;
    }

    /**
     *
     */
    void LRAOneModule::initialize()
    {
        for( set<const Constraint*, constraintPointerComp>::const_iterator iter = mLinearConstraints.begin();
             iter != mLinearConstraints.end(); ++iter )
        {
            map<const string, numeric, strCmp> coeffs = (**iter).linearAndConstantCoefficients();
            assert( coeffs.size() > 1 );
            map<const string, numeric, strCmp>::iterator currentCoeff = coeffs.begin();
            ex*                                          linearPart   = new ex( (*iter)->lhs() - currentCoeff->second );
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
                ex*                     var       = new ex( (*(**iter).variables().begin()).second );
                ExVariableMap::iterator basicIter = mExistingVars.find( var );
                // constraint not found, add new nonbasic variable
                if( basicIter == mExistingVars.end() )
                {
                    Variable* nonBasic = mTableau.newNonbasicVariable( var );
                    mExistingVars.insert( pair<const ex*, Variable*>( var, nonBasic ) );
                    setBound( *nonBasic, (**iter).relation(), highestCoeff.is_negative(), -coeffs.begin()->second, *iter );
                }
                else
                {
                    delete var;
                    Variable* nonBasic = (*basicIter).second;
                    setBound( *nonBasic, (**iter).relation(), highestCoeff.is_negative(), -coeffs.begin()->second, *iter );
                }

            }
            else
            {
                ExVariableMap::iterator slackIter = mExistingVars.find( linearPart );
                if( slackIter == mExistingVars.end() )
                {
                    vector< Variable* > nonbasics = vector< Variable* >();
                    vector< numeric > numCoeffs = vector< numeric >();
                    symtab::const_iterator                       varIt   = (**iter).variables().begin();
                    map<const string, numeric, strCmp>::iterator coeffIt = coeffs.begin();
                    ++coeffIt;
                    while( varIt != (**iter).variables().end() )
                    {
                        assert( coeffIt != coeffs.end() );
                        ex*                     var          = new ex( (*varIt).second );
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
                            nonbasics.push_back( (*nonBasicIter).second );
                        }
                        numCoeffs.push_back( coeffIt->second );
                        ++varIt;
                        ++coeffIt;
                    }

                    Variable* slackVar = mTableau.newBasicVariable( linearPart, nonbasics, numCoeffs );

                    mExistingVars.insert( pair<const ex*, Variable*>( linearPart, slackVar ) );
                    setBound( *slackVar, (**iter).relation(), highestCoeff.is_negative(), -coeffs.begin()->second, *iter );
                }
                else
                {
                    delete linearPart;
                    Variable* slackVar = (*slackIter).second;
                    setBound( *slackVar, (**iter).relation(), highestCoeff.is_negative(), -coeffs.begin()->second, *iter );
                }
            }
        }
        mInitialized = true;
    }

    /**
     *
     * @param _var
     * @param bound
     * @return
     */
    bool LRAOneModule::activateBound( Variable& _var, const Bound* bound )
    {
        assert( _var.pSupremum() != NULL );
        bool isUpper = bound->isUpper();
        _var.setActive( bound, true );
        if( isUpper )
        {
            if( *_var.pInfimum() > *bound )
            {
                return false;
            }
            if( *_var.pSupremum() > *bound )
            {
                _var.setSupremum( bound );

                if( !_var.getBasic() && (*_var.pSupremum() < _var.assignment()) )
                {
                    mTableau.updateBasicAssignments( _var.position(), Value( (*_var.pSupremum()).limit() - _var.assignment() ) );
                    _var.rAssignment() = (*_var.pSupremum()).limit();
                }
            }
        }
        else
        {
            if( *_var.pSupremum() < *bound )
            {
                return false;
            }
            //check if the new lower bound is bigger
            if( *_var.pInfimum() < *bound )
            {
                _var.setInfimum( bound );

                if( !_var.getBasic() && (*_var.pInfimum() > _var.assignment()) )
                {
                    mTableau.updateBasicAssignments( _var.position(), Value( (*_var.pInfimum()).limit() - _var.assignment() ) );
                    _var.rAssignment() = (*_var.pInfimum()).limit();
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
    void LRAOneModule::setBound( Variable& var, const Constraint_Relation& rel, bool constraintInverted, const numeric& boundValue, const Constraint* constr )
    {
        if( rel == CR_EQ )
        {
            Value*       value  = new Value( boundValue );
            const Bound* ubound = var.addUpperBound( value );
            mBoundToConstraint[ubound] = constr;
            const Bound*         lbound   = var.addLowerBound( value );
            vector<const Bound*> eqBounds = vector<const Bound*>();
            eqBounds.push_back( ubound );
            eqBounds.push_back( lbound );

            ConstraintBoundPair p      = ConstraintBoundPair( constr, eqBounds );
            mBoundToConstraint[lbound] = constr;
            mConstraintToBound.insert( p );
        }
        else if( rel == CR_LEQ )
        {
            Value*                                       value = new Value( boundValue );
            const Bound*                                 bound = (constraintInverted ? var.addLowerBound( value ) : var.addUpperBound( value ));
            pair<const Bound* const , const Constraint*> p2    = pair<const Bound* const , const Constraint*>( bound, constr );
            mBoundToConstraint.insert( p2 );
            vector<const Bound*> vecto = vector<const Bound*>();
            vecto.push_back( bound );
            ConstraintBoundPair p = ConstraintBoundPair( constr, vecto );

            mConstraintToBound.insert( p );
        }
        else if( rel == CR_GEQ )
        {
            Value*                                       value = new Value( boundValue );
            const Bound*                                 bound = (constraintInverted ? var.addUpperBound( value ) : var.addLowerBound( value ));
            pair<const Bound* const , const Constraint*> p2    = pair<const Bound* const , const Constraint*>( bound, constr );
            mBoundToConstraint.insert( p2 );
            vector<const Bound*> vecto = vector<const Bound*>();
            vecto.push_back( bound );
            ConstraintBoundPair p = ConstraintBoundPair( constr, vecto );

            mConstraintToBound.insert( p );
        }
        else if( rel == CR_LESS )
        {
            Value*                                       value = new Value( boundValue, (constraintInverted ? 1 : -1) );
            const Bound*                                 bound = (constraintInverted ? var.addLowerBound( value ) : var.addUpperBound( value ));
            pair<const Bound* const , const Constraint*> p2    = pair<const Bound* const , const Constraint*>( bound, constr );
            mBoundToConstraint.insert( p2 );
            vector<const Bound*> vecto = vector<const Bound*>();
            vecto.push_back( bound );
            ConstraintBoundPair p = ConstraintBoundPair( constr, vecto );

            mConstraintToBound.insert( p );
        }
        else if( rel == CR_GREATER )
        {
            Value*                                       value = new Value( boundValue, (constraintInverted ? -1 : 1) );
            const Bound*                                 bound = (constraintInverted ? var.addUpperBound( value ) : var.addLowerBound( value ));
            pair<const Bound* const , const Constraint*> p2    = pair<const Bound* const , const Constraint*>( bound, constr );
            mBoundToConstraint.insert( p2 );
            vector<const Bound*> vecto = vector<const Bound*>();
            vecto.push_back( bound );
            ConstraintBoundPair p = ConstraintBoundPair( constr, vecto );

            mConstraintToBound.insert( p );
        }
    }
}    // namespace smtrat

