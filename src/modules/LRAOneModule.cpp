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
        mAllVars(),
        mLinearConstraints(),
        mNonlinearConstraints(),
        mInitialized( false ),
        mRowMaximum( 0 ),
        mColumnMaximum( 0 ),
        mPivotCoeff( 0 ),
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

                //iterate through boundvector, nescassary for equal
                for( vector<const Bound*>::const_iterator bIter = boundL.begin(); bIter != boundL.end(); ++bIter )
                {
                    if( !activateBound( *(*bIter)->pVariable(), *bIter ) )
                    {
                        // Bound creates directly a conflict
                        const Variable* var = (*bIter)->pVariable();
                        if( (*bIter)->isUpper() )
                        {
                            BoundActivityMap::const_iterator bound = var->lowerbounds().begin(); //TODO: Start with the infimum. This needs that it is stored as iterator.
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
                            BoundActivityMap::const_iterator bound = var->upperbounds().begin(); //TODO: Start with the supremum. This needs that it is stored as iterator.
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
            printVariables();
            cout << endl;
            printTableau();
            cout << endl;
            #endif
            // Search for a basic variable which violates its bound
            Variable * basicVar;
            const Bound* violatedBound = NULL;
            vector<Variable*>::const_iterator basicIt = mAllVars.begin();
            while( basicIt != mAllVars.end() )
            {
                if( (**basicIt).getBasic() )
                {
                    if( *(**basicIt).pSupremum() < (**basicIt).rAssignment() )
                    {
                        basicVar           = *basicIt;
                        violatedBound      = (**basicIt).pSupremum();
                        break;
                    }
                    else if( *(**basicIt).pInfimum() > (**basicIt).rAssignment() )
                    {
                        basicVar           = *basicIt;
                        violatedBound      = (**basicIt).pInfimum();
                        break;
                    }
                }
                ++basicIt;
            }
            // Found a solution
            if( violatedBound == NULL )
            {
                #ifdef DEBUG_LRA_MODULE
                cout << "True" << endl;
                #endif
                return (checkAssignmentForNonlinearConstraint() ? True : Unknown );
            }

            unsigned i = basicVar->position();
            if( !isInConflict( i, violatedBound->isUpper() ) )
            {
                pivotAndUpdate( basicVar, mPivotNonBasicVar, *violatedBound, mPivotCoeff );
            }
            else
            {
                while( basicIt != mAllVars.end() )
                {
                    if( (**basicIt).getBasic() )
                    {
                        violatedBound = NULL;
                        if( *(**basicIt).pSupremum() < (**basicIt).rAssignment() )
                        {
                            violatedBound = (**basicIt).pSupremum();
                        }
                        else if( *(**basicIt).pInfimum() > (**basicIt).rAssignment() )
                        {
                            violatedBound = (**basicIt).pInfimum();
                        }
                        if( violatedBound != NULL )
                        {
                            bool upperBoundViolated = violatedBound->isUpper();
                            if( isInConflict( (**basicIt).position(), upperBoundViolated ) )
                            {
                                getConflicts( **basicIt, upperBoundViolated );
                            }
                        }
                    }
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
     * @param basicVar
     * @param nonBasicVar
     * @param bound
     * @param coeff
     */
    void LRAOneModule::pivotAndUpdate( Variable* basicVar, Variable* nonBasicVar, const Bound& bound, numeric& coeff )
    {
        assert( !bound.isInfinite() );
        cout << "pivotAndUpdate" << endl;
        basicVar->print();
        nonBasicVar->print();
        bound.print( cout, true );
        cout << endl << "coeff = ";
        coeff.print( cout );
        cout << endl;
        Value theta = (bound.limit() - basicVar->rAssignment()) / coeff;
        cout << "theta = ";
        theta.print( cout );
        cout << endl;
        // Update the assignment of the basic variable to pivot
        cout << "beta(basicvar) = ";
        basicVar->rAssignment().print( cout );
        cout << endl;
        basicVar->wAssignment( bound.limit() );
        cout << "beta(basicvar) = ";
        basicVar->rAssignment().print( cout );
        cout << endl;
        // Update the assignment of the non basic variable to pivot
        cout << "beta(nonBasicVar) = ";
        nonBasicVar->rAssignment().print( cout );
        cout << endl;
        nonBasicVar->wAssignment( nonBasicVar->rAssignment() + theta );
        cout << "beta(nonBasicVar) = ";
        nonBasicVar->rAssignment().print( cout );
        cout << endl;
        // Update the assignments of all basic variables.
        cout << "Now the other basic variables:" << endl;
        unsigned columnNumber = nonBasicVar->position();
        for( vector<Variable*>::const_iterator basicIt = mAllVars.begin(); basicIt != mAllVars.end(); ++basicIt )
        {
            if( (**basicIt).getBasic() && (*basicIt) != basicVar )
            {
                Tableau::iterator it = mTableau.find( Position( (*basicIt)->position(), columnNumber ) );
                if( !(it == mTableau.end()) )
                {
                    cout << "beta(basicvar) = ";
                    (*basicIt)->rAssignment().print( cout );
                    cout << endl;
                    (*basicIt)->wAssignment( (*basicIt)->rAssignment() + Value( theta * it->second ) );
                    cout << "beta(basicvar) = ";
                    (*basicIt)->rAssignment().print( cout );
                    cout << endl;
                }
            }
        }
        // Pivot the given basic and non basic variable
        unsigned column = nonBasicVar->position();
        nonBasicVar->wPosition( basicVar->position() );
        nonBasicVar->setBasic( true );
        basicVar->wPosition( column );
        basicVar->setBasic( false );
        //TODO: update the tableau
        // 1.) Divide all entries of the row at basicVar->position() by coeff
        // 2.) Update all the other rows i having (i,nonBasicVar->position()) non zero:
        //     2.1) the entry is   1/coeff      , if i=nonBasicVar->position()
        //     2.2) subtract       entry/coeff  , otherwise
    }

    /**
     *
     * @param i
     * @param isUpperBoundViolated
     * @return
     */
    bool LRAOneModule::isInConflict( unsigned i, bool isUpperBoundViolated )
    {
        unsigned j;
        Position tableauIndex;
        for( vector<Variable*>::const_iterator nonBasicIt = mAllVars.begin(); nonBasicIt != mAllVars.end(); ++nonBasicIt )
        {
            if( !(**nonBasicIt).getBasic() )
            {
                j = (*nonBasicIt)->position();
                // TODO: maybe try map from coefficients to variable
                tableauIndex = Position( i, j );
                // Problem: coefficient could be zero and thus non existent
                // Searching for every pair i,j destroys the efficiency
                Tableau::iterator it = mTableau.find( tableauIndex );
                if( !(it == mTableau.end()) )
                {
                    if( isUpperBoundViolated )
                    {
                        if( (*(**nonBasicIt).pSupremum() > (**nonBasicIt).rAssignment() && it->second < 0)
                                || (*(**nonBasicIt).pInfimum() < (**nonBasicIt).rAssignment() && it->second > 0) )
                        {
                            //nonbasic variable can be increased
                            mPivotNonBasicVar = *nonBasicIt;
                            mPivotCoeff       = it->second;
                            return false;
                        }
                    }
                    else
                    {
                        if( (*(**nonBasicIt).pSupremum() > (**nonBasicIt).rAssignment() && it->second > 0)
                                || (*(**nonBasicIt).pInfimum() < (**nonBasicIt).rAssignment() && it->second < 0) )
                        {
                            //nonbasic variable can be increased
                            mPivotNonBasicVar = *nonBasicIt;
                            mPivotCoeff       = it->second;
                            return false;
                        }

                    }
                }
            }
        }
        return true;
    }

    /**
     *
     * @param i
     * @param isUpperBoundViolated
     */
    void LRAOneModule::getConflicts( const Variable& _variable, bool isUpperBoundViolated )
    {
        unsigned            j;
        set<const Formula*> infeasibleSubset = set<const Formula*>();
        // Add the constraint of the variable to the infeasible subset
        if( isUpperBoundViolated )
        {
            infeasibleSubset.insert( getSubformula( _variable.pSupremum() ) );
        }
        else
        {
            infeasibleSubset.insert( getSubformula( _variable.pInfimum() ) );
        }
        Position            tableauIndex;
        for( vector<Variable*>::const_iterator nonBasicIt = mAllVars.begin(); nonBasicIt != mAllVars.end(); ++nonBasicIt )
        {
            if( !(**nonBasicIt).getBasic() )
            {
                j            = (*nonBasicIt)->position();
                tableauIndex = Position( _variable.position(), j );
                Tableau::iterator it = mTableau.find( tableauIndex );
                if( !(it == mTableau.end()) )
                {
                    //coeff != 0, variable occurs
                    if( (isUpperBoundViolated && it->second < 0) || (!isUpperBoundViolated && it->second > 0) )
                    {
                        infeasibleSubset.insert( getSubformula( (**nonBasicIt).pSupremum() ) );
                    }
                    else
                    {
                        assert( (isUpperBoundViolated && it->second > 0) || (!isUpperBoundViolated && it->second < 0) );
                        infeasibleSubset.insert( getSubformula( (**nonBasicIt).pInfimum() ) );
                    }

                }
            }
        }
        Module::mInfeasibleSubsets.push_back( infeasibleSubset );
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
     * @param isBasic
     * @param position
     * @return
     */
    Variable* LRAOneModule::getVar( bool isBasic, unsigned position )
    {
        for( vector<Variable*>::const_iterator varIt = mAllVars.begin(); varIt != mAllVars.end(); ++varIt )
        {
            if( (**varIt).getBasic() == isBasic && (*varIt)->position() == position )
            {
                return *varIt;
            }
        }
        assert( false );
        return NULL;
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

            //divide the linear Part and constraint by the highest coefficient
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
                //Constraint has one variable
                for( symtab::const_iterator varIt = (**iter).variables().begin(); varIt != (**iter).variables().end(); ++varIt )
                {
                    ex*                     var       = new ex( (*varIt).second );
                    ExVariableMap::iterator basicIter = mExistingVars.find( var );
                    //constraint not found, add new nonbasic variable
                    if( basicIter == mExistingVars.end() )
                    {
                        Variable* nonBasic = new Variable( 1, mColumnMaximum, false, var );
                        mExistingVars.insert( pair<const ex*, Variable*>( var, nonBasic ) );
                        mAllVars.push_back( nonBasic );
                        mColumnMaximum++;
                        setBound( *nonBasic, (**iter).relation(), highestCoeff.is_negative(), coeffs.begin()->second, *iter );
                    }
                    else
                    {
                        delete var;
                        Variable* nonBasic = (*basicIter).second;
                        setBound( *nonBasic, (**iter).relation(), highestCoeff.is_negative(), coeffs.begin()->second, *iter );
                    }
                }

            }
            else
            {
                ExVariableMap::iterator slackIter = mExistingVars.find( linearPart );
                if( slackIter == mExistingVars.end() )
                {
                    Variable* slackVar = new Variable( 1, mRowMaximum, true, linearPart );
                    //See if variable already exists
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
                            Variable* nonBasic = new Variable( 1, mColumnMaximum, false, var );
                            mExistingVars.insert( pair<const ex*, Variable*>( var, nonBasic ) );
                            mColumnMaximum++;
                            Position p1 = Position( mRowMaximum, nonBasic->position() );
                            pair<Position, numeric> p2 = pair<Position, numeric>( p1, coeffIt->second );
                            mTableau.insert( p2 );
                            mAllVars.push_back( nonBasic );
                        }
                        else
                        {
                            delete var;
                            Variable* nonBasic = (*nonBasicIter).second;
                            Position p1 = Position( mRowMaximum, nonBasic->position() );
                            pair<Position, numeric> p2 = pair<Position, numeric>( p1, coeffIt->second );
                            mTableau.insert( p2 );
                        }
                        ++varIt;
                        ++coeffIt;
                    }

                    mExistingVars.insert( pair<const ex*, Variable*>( linearPart, slackVar ) );
                    mAllVars.push_back( slackVar );
                    mRowMaximum++;
                    setBound( *slackVar, (**iter).relation(), highestCoeff.is_negative(), coeffs.begin()->second, *iter );
                }
                else
                {
                    delete linearPart;
                    Variable* slackVar = (*slackIter).second;
                    setBound( *slackVar, (**iter).relation(), highestCoeff.is_negative(), coeffs.begin()->second, *iter );
                }
            }
        }
        initPriority();
        mInitialized = true;
    }

    /**
     *
     */
    void LRAOneModule::initPriority()
    {
        // TODO: Sort the vector according to a variable order heuristic and set the priorities of the variables
        // or maybe there is no need of the priorities of the variables anymore
        unsigned prior = 0;
        for( vector<Variable*>::const_iterator varIt = mAllVars.begin(); varIt != mAllVars.end(); ++varIt )
        {
            (**varIt).wPriority( prior );
            prior++;
        }
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
        //isAnUpperBound
        if( isUpper )
        {
            if( *_var.pInfimum() > *bound )
            {
                return false;
            }
            //current smallest upper bound
            if( *_var.pSupremum() > *bound )
            {
                //change the position of the smallest upper bound to the position of the new bound
                _var.setSupremum( bound );

                if( !_var.getBasic() && (*_var.pSupremum() < _var.rAssignment()) )
                {
                    _var.wAssignment( (*_var.pSupremum()).limit() );
                    for( vector<Variable*>::const_iterator iter = mAllVars.begin(); iter != mAllVars.end(); ++iter )
                    {
                        if( (*iter)->getBasic() )
                        {
                            Position p = Position( (*iter)->position(), _var.position() );
                            Tableau::iterator tabIt = mTableau.find( p );
                            if( tabIt != mTableau.end() )
                            {
                                (*iter)->wAssignment( (*_var.pSupremum()).limit() );
                            }
                        }
                    }
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

                if( !_var.getBasic() && (*_var.pInfimum() > _var.rAssignment()) )
                {
                    _var.wAssignment( (*_var.pInfimum()).limit() );
                    for( vector<Variable*>::const_iterator iter = mAllVars.begin(); iter != mAllVars.end(); ++iter )
                    {
                        if( (*iter)->getBasic() )
                        {
                            Position p = Position( (*iter)->position(), _var.position() );
                            Tableau::iterator tabIt = mTableau.find( p );
                            if( tabIt != mTableau.end() )
                            {
                                (*iter)->wAssignment( (*_var.pInfimum()).limit() );
                            }
                        }
                    }
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
    void LRAOneModule::setBound( Variable& var, const Constraint_Relation& rel, bool negativ, numeric& boundValue, const Constraint* constr )
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
            const Bound*                                 bound = (negativ ? var.addLowerBound( value ) : var.addUpperBound( value ));
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
            const Bound*                                 bound = (negativ ? var.addUpperBound( value ) : var.addLowerBound( value ));
            pair<const Bound* const , const Constraint*> p2    = pair<const Bound* const , const Constraint*>( bound, constr );
            mBoundToConstraint.insert( p2 );
            vector<const Bound*> vecto = vector<const Bound*>();
            vecto.push_back( bound );
            ConstraintBoundPair p = ConstraintBoundPair( constr, vecto );

            mConstraintToBound.insert( p );
        }
        else if( rel == CR_LESS )
        {
            Value*                                       value = new Value( boundValue, (negativ ? 1 : -1) );
            const Bound*                                 bound = (negativ ? var.addLowerBound( value ) : var.addUpperBound( value ));
            pair<const Bound* const , const Constraint*> p2    = pair<const Bound* const , const Constraint*>( bound, constr );
            mBoundToConstraint.insert( p2 );
            vector<const Bound*> vecto = vector<const Bound*>();
            vecto.push_back( bound );
            ConstraintBoundPair p = ConstraintBoundPair( constr, vecto );

            mConstraintToBound.insert( p );
        }
        else if( rel == CR_GREATER )
        {
            Value*                                       value = new Value( boundValue, (negativ ? -1 : 1) );
            const Bound*                                 bound = (negativ ? var.addUpperBound( value ) : var.addLowerBound( value ));
            pair<const Bound* const , const Constraint*> p2    = pair<const Bound* const , const Constraint*>( bound, constr );
            mBoundToConstraint.insert( p2 );
            vector<const Bound*> vecto = vector<const Bound*>();
            vecto.push_back( bound );
            ConstraintBoundPair p = ConstraintBoundPair( constr, vecto );

            mConstraintToBound.insert( p );
        }
    }

    /**
     *
     * @param _out
     */
    void LRAOneModule::printVariables( ostream& _out ) const
    {
        _out << "Variables:" << endl;
        for( vector<Variable*>::const_iterator varIt = mAllVars.begin(); varIt != mAllVars.end(); ++varIt )
        {
            _out << "  ";
            (*varIt)->print( _out );
        }
    }

    /**
     *
     * @param _out
     */
    void LRAOneModule::printTableau( ostream& _out ) const
    {
        unsigned maxlength     = 15;    // how many digit positions it should take up
        unsigned currentrow    = 0;
        unsigned currentcolumn = 0;
        char     frameSign     = '-';
        _out << setw( maxlength * (mColumnMaximum + 1) ) << setfill( frameSign ) << "" << endl;
        _out << setw( maxlength ) << setfill( ' ' ) << "#";
        for( unsigned i = 0; i < mColumnMaximum; ++i )
        {
            for( vector<Variable*>::const_iterator var = mAllVars.begin(); var != mAllVars.end(); ++var )
            {
                if( (*var)->position() == i &&!(*var)->getBasic() )
                {
                    stringstream out;
                    out << *(*var)->pExpression();
                    _out << setw( maxlength ) << out.str() + " #";
                }
            }
        }
        _out << endl;
        _out << setw( maxlength * (mColumnMaximum + 1) ) << setfill( '#' ) << "" << endl;
        _out << setfill( ' ' );
        for( vector<Variable*>::const_iterator var = mAllVars.begin(); var != mAllVars.end(); ++var )
        {
            if( (*var)->position() == 0 && (*var)->getBasic() )
            {
                stringstream out;
                out << *(*var)->pExpression();
                _out << setw( maxlength ) << out.str() + " #";
            }
        }
        for( Tableau::const_iterator iter = mTableau.begin(); iter != mTableau.end(); ++iter )
        {
            if( (*iter).first.first > currentrow )
            {
                for( unsigned i = currentcolumn; i < mColumnMaximum; ++i )
                {
                    _out << setw( maxlength ) << "0 #";
                }
                _out << endl;
                ++currentrow;
                for( vector<Variable*>::const_iterator var = mAllVars.begin(); var != mAllVars.end(); ++var )
                {
                    if( (*var)->position() == currentrow && (*var)->getBasic() )
                    {
                        stringstream out;
                        out << *(*var)->pExpression();
                        _out << setw( maxlength ) << out.str() + " #";
                    }
                }
                currentcolumn = 0;
            }
            while( currentcolumn < (*iter).first.second )
            {
                _out << setw( maxlength ) << "0 #";
                ++currentcolumn;
            }

            stringstream out;
            out << (*iter).second;
            _out << setw( maxlength ) << out.str() + " #";
            ++currentcolumn;
        }
        for( unsigned i = currentcolumn; i < mColumnMaximum; ++i )
        {
            _out << setw( maxlength ) << "0 #";
        }
        _out << endl;
        _out << setw( maxlength * (mColumnMaximum + 1) ) << setfill( frameSign ) << "" << endl;
        _out << setfill( ' ' );
    }

}    // namespace smtrat

