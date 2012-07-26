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
        mAllConstraints(),
        mInitialized( false ),
        mRowMaximum( 0 ),
        mColumnMaximum( 0 ),
        mPivotCoeff( 0 ),
        mExistingVars(),
        mBoundToConstraint(),
        mConstraintToFormula(),
        mConstraintToBound()
    {
        this->mModuleType = MT_LRAOneModule;
    }

    /**
     * Destructor:
     */
    LRAOneModule::~LRAOneModule(){}

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
        cout << "inform about " << *_constraint << endl;
        if( _constraint->isConsistent() == 2 )
        {
            mAllConstraints.push_back( _constraint );
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
        cout << "assert " << (*_subformula)->constraint() << endl;
        Module::assertSubformula( _subformula );
        if( !mInitialized )
        {
            initialize();
        }

        const Constraint* constraint  = (*_subformula)->pConstraint();
        int               consistency = constraint->isConsistent();
        if( consistency == 2 )
        {
            pair<const Constraint*, const Formula* const > cFpair = pair<const Constraint*, const Formula* const >( constraint, *_subformula );
            mConstraintToFormula.insert( cFpair );
            ConstraintBoundMap::iterator iter = mConstraintToBound.find( constraint );

            assert( iter != mConstraintToBound.end() );

            vector<const Bound*> boundL = (*iter).second;

            //iterate through boundvector, nescassary for equal
            for( vector<const Bound*>::const_iterator bIter = boundL.begin(); bIter != boundL.end(); ++bIter )
            {
                activateBound( *(*bIter)->pVariable(), *bIter );
            }
            return true;
        }
        else
        {
            return (consistency == 1);
        }
    }

    /**
     *
     * @return
     */
    Answer LRAOneModule::isConsistent()
    {
        cout << "check for consistency" << endl;
        while( true )
        {
            printTableau();
            Variable * basicVar;
            bool         upperBoundViolated = false;
            bool         lowerBoundViolated = false;
            const Bound* violatedBound;
            for( vector<Variable*>::const_iterator basicIt = mAllVars.begin(); basicIt != mAllVars.end(); ++basicIt )
            {
                if( (**basicIt).getBasic() )
                {
                    if( *(**basicIt).getSupremum() < (**basicIt).rAssignment() )
                    {
                        upperBoundViolated = true;
                        basicVar           = *basicIt;
                        violatedBound      = (**basicIt).getSupremum();
                        break;
                    }
                    else if( *(**basicIt).getInfimum() > (**basicIt).rAssignment() )
                    {
                        lowerBoundViolated = true;
                        basicVar           = *basicIt;
                        violatedBound      = (**basicIt).getInfimum();
                        break;
                    }
                }
            }
            if( !(upperBoundViolated || lowerBoundViolated) )
            {
                Module::print();
                return True;    // SAT
            }
            assert( !(upperBoundViolated && lowerBoundViolated) );

            unsigned i = basicVar->rPosition();

            if( !isInConflict( i, upperBoundViolated ) )
            {
                pivotAndUpdate( basicVar, mPivotNonBasicVar, *violatedBound, mPivotCoeff );
            }
            else
            {
                //TODO: return infeasible subset
                //iterate through every row
                mInfeasibleSubsets.clear();
                for( vector<Variable*>::const_iterator basicIt = mAllVars.begin(); basicIt != mAllVars.end(); ++basicIt )
                {
                    if( (**basicIt).getBasic() )
                    {
                        lowerBoundViolated = false;
                        upperBoundViolated = false;
                        if( *(**basicIt).getSupremum() < (**basicIt).rAssignment() )
                        {
                            upperBoundViolated = true;
                        }
                        else if( *(**basicIt).getInfimum() > (**basicIt).rAssignment() )
                        {
                            lowerBoundViolated = true;
                        }
                        if( lowerBoundViolated || upperBoundViolated )
                        {
                            if( isInConflict( (**basicIt).rPosition(), upperBoundViolated ) )
                            {
                                getConflicts( (**basicIt).rPosition(), upperBoundViolated );
                            }
                        }
                    }
                }
                Module::print();
                return False;
            }
        }
        assert( false );
        return True;
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
        Value test       = bound.limit();
        Value theta      = (test - basicVar->rAssignment()) / coeff;
        Value assignment = bound.limit();
        basicVar->wAssignment( assignment );
        assignment = nonBasicVar->rAssignment() + theta;
        nonBasicVar->wAssignment( assignment );
        unsigned i;
        unsigned j = nonBasicVar->rPosition();
        Position tableauIndex;
        for( vector<Variable*>::const_iterator basicIt = mAllVars.begin(); basicIt != mAllVars.end(); ++basicIt )
        {
            if( (**basicIt).getBasic() && (*basicIt) != basicVar )
            {
                //comparing pointers could be troublesome
                i            = (*basicIt)->rPosition();
                tableauIndex = Position( i, j );
                Tableau::iterator it = mTableau.find( tableauIndex );
                if( !(it == mTableau.end()) )
                {
                    numeric coeffic = mTableau.at( tableauIndex );
                    Value rest      = theta * coeffic;
                    assignment      = (*basicIt)->rAssignment() + rest;
                    (*basicIt)->wAssignment( assignment );
                }
            }
        }
        unsigned column = nonBasicVar->rPosition();
        nonBasicVar->wPosition( basicVar->rPosition() );
        nonBasicVar->setBasic( true );
        basicVar->wPosition( column );
        basicVar->setBasic( false );
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
                j = (*nonBasicIt)->rPosition();
                // TODO: maybe try map from coefficients to variable
                tableauIndex = Position( i, j );
                // Problem: coefficient could be zero and thus non existent
                // Searching for every pair i,j destroys the efficiency
                Tableau::iterator it = mTableau.find( tableauIndex );
                if( !(it == mTableau.end()) )
                {
                    if( isUpperBoundViolated )
                    {
                        if( (*(**nonBasicIt).getSupremum() > (**nonBasicIt).rAssignment() && it->second < 0)
                                || (*(**nonBasicIt).getInfimum() < (**nonBasicIt).rAssignment() && it->second > 0) )
                        {
                            //nonbasic variable can be increased
                            mPivotNonBasicVar = *nonBasicIt;
                            mPivotCoeff       = it->second;
                            return false;
                        }
                    }
                    else
                    {
                        if( (*(**nonBasicIt).getSupremum() > (**nonBasicIt).rAssignment() && it->second > 0)
                                || (*(**nonBasicIt).getInfimum() < (**nonBasicIt).rAssignment() && it->second < 0) )
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
    void LRAOneModule::getConflicts( unsigned i, bool isUpperBoundViolated )
    {
        unsigned            j;
        const Constraint*   constraint;
        set<const Formula*> infeasibleSubset = set<const Formula*>();
        Position            tableauIndex;
        for( vector<Variable*>::const_iterator nonBasicIt = mAllVars.begin(); nonBasicIt != mAllVars.end(); ++nonBasicIt )
        {
            if( !(**nonBasicIt).getBasic() )
            {
                j            = (*nonBasicIt)->rPosition();
                tableauIndex = Position( i, j );
                Tableau::iterator it = mTableau.find( tableauIndex );
                if( !(it == mTableau.end()) )
                {
                    //coeff != 0, variable occurs
                    if( (isUpperBoundViolated && it->second < 0) || (!isUpperBoundViolated && it->second > 0) )
                    {
                        const Bound*                                                  b  = (**nonBasicIt).getSupremum();
                        BoundConstraintMap::iterator it = mBoundToConstraint.find( b );
                        assert( it != mBoundToConstraint.end() );
                        constraint = (*it).second;
                        ConstraintFormulaMap::iterator consToForm = mConstraintToFormula.find( constraint );
                        assert( consToForm != mConstraintToFormula.end() );
                        infeasibleSubset.insert( consToForm->second );
                    }
                    else
                    {
                        assert( (isUpperBoundViolated && it->second > 0) || (!isUpperBoundViolated && it->second < 0) );
                        const Bound*                                                  b  = (**nonBasicIt).getInfimum();
                        BoundConstraintMap::iterator it = mBoundToConstraint.find( b );
                        assert( it != mBoundToConstraint.end() );
                        constraint = (*it).second;
                        ConstraintFormulaMap::iterator consToForm = mConstraintToFormula.find( constraint );
                        assert( consToForm != mConstraintToFormula.end() );
                        infeasibleSubset.insert( consToForm->second );
                    }

                }
            }
        }
        Module::mInfeasibleSubsets.push_back( infeasibleSubset );
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
            if( (**varIt).getBasic() == isBasic && (**varIt).rPosition() == position )
            {
                return *varIt;
            }
        }
        assert( false );
        return NULL;
    }

    /**
     *
     * @param _subformula
     */
    void LRAOneModule::removeSubformula( Formula::const_iterator _subformula )
    {
        //TODO:deactivate Flag for activation
        //and reset the lowest upper bound, and the highest lower bound
        const Constraint* constraint = (*_subformula)->pConstraint();
        mConstraintToFormula.erase( constraint );
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
     */
    void LRAOneModule::initialize()
    {
        for( vector<const Constraint*>::const_iterator iter = mAllConstraints.begin(); iter != mAllConstraints.end(); ++iter )
        {
            map<const string, numeric, strCmp> coeffs = (**iter).linearAndConstantCoefficients();
            assert( coeffs.size() > 1 );
            map<const string, numeric, strCmp>::iterator currentCoeff = coeffs.begin();
            ex*                                          linearPart   = new ex( (*iter)->lhs() - currentCoeff->second );
            ++currentCoeff;

            //divide the linear Part and constraint by the highest coefficient
            numeric highestCoeff = currentCoeff->second;
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
                        Variable* nonBasic = new Variable( 1, mColumnMaximum, false );
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
                    Variable* slackVar = new Variable( 1, mRowMaximum, true );
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
                            Variable* nonBasic = new Variable( 1, mColumnMaximum, false );
                            mExistingVars.insert( pair<const ex*, Variable*>( var, nonBasic ) );
                            mColumnMaximum++;
                            Position p1 = Position( mRowMaximum, nonBasic->rPosition() );
                            pair<Position, numeric> p2 = pair<Position, numeric>( p1, coeffIt->second );
                            mTableau.insert( p2 );
                            mAllVars.push_back( nonBasic );
                        }
                        else
                        {
                            delete var;
                            Variable* nonBasic = (*nonBasicIter).second;
                            Position p1 = Position( mRowMaximum, nonBasic->rPosition() );
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
     */
    void LRAOneModule::activateBound( Variable& _var, const Bound* bound )
    {
        assert( _var.getSupremum() != NULL );
        bool isUpper = (*bound).getIsUpper();
        _var.setActive( bound, true );
        //isAnUpperBound
        if( isUpper )
        {
            //current smallest upper bound
            if( *_var.getSupremum() > *bound )
            {
                //change the position of the smallest upper bound to the position of the new bound
                _var.setSupremum( bound );

                if( !_var.getBasic() && (*_var.getSupremum() < _var.rAssignment()) )
                {
                    _var.wAssignment( (*_var.getSupremum()).limit() );
                    for( vector<Variable*>::const_iterator iter = mAllVars.begin(); iter != mAllVars.end(); ++iter )
                    {
                        if( (*iter)->getBasic() )
                        {
                            Position p = Position( (*iter)->rPosition(), _var.rPosition() );
                            Tableau::iterator tabIt = mTableau.find( p );
                            if( tabIt != mTableau.end() )
                            {
                                (*iter)->wAssignment( (*_var.getSupremum()).limit() );
                            }
                        }
                    }
                }
            }
            //update assignment
        }
        else
        {
            //check if the new lower bound is bigger
            if( *_var.getInfimum() < *bound )
            {
                _var.setInfimum( bound );
            }
            if( !_var.getBasic() && (*_var.getInfimum() > _var.rAssignment()) )
            {
                _var.wAssignment( (*_var.getInfimum()).limit() );
                for( vector<Variable*>::const_iterator iter = mAllVars.begin(); iter != mAllVars.end(); ++iter )
                {
                    if( (*iter)->getBasic() )
                    {
                        Position p = Position( (*iter)->rPosition(), _var.rPosition() );
                        Tableau::iterator tabIt = mTableau.find( p );
                        if( tabIt != mTableau.end() )
                        {
                            (*iter)->wAssignment( (*_var.getInfimum()).limit() );
                        }
                    }
                }
            }
        }
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
    void LRAOneModule::printAssignments( ostream& _out ) const
    {
        _out << "Assignments:" << endl;
        for( vector<Variable*>::const_iterator varIt = mAllVars.begin(); varIt != mAllVars.end(); ++varIt )
        {
            _out << "Assignment = ";
            (**varIt).rAssignment().print();
            _out << endl;
        }
    }

    /**
     *
     * @param _out
     */
    void LRAOneModule::printVariables( ostream& _out ) const
    {
        for( vector<Variable*>::const_iterator varIt = mAllVars.begin(); varIt != mAllVars.end(); ++varIt )
        {
            (*varIt)->print( _out );
        }
    }

    /**
     *
     * @param _out
     */
    void LRAOneModule::printTableau( ostream& _out ) const
    {
        unsigned maxlength     = 10;    // how many digit positions it should take up
        unsigned currentrow    = 0;
        unsigned currentcolumn = 0;
        char     frameSign     = '-';
        _out << setw( maxlength * (mColumnMaximum + 1) ) << setfill( frameSign ) << "" << endl;
        _out << setw( maxlength ) << setfill( ' ' ) << "#";
        for( unsigned i = 0; i < mColumnMaximum; ++i )
        {
            for( vector<Variable*>::const_iterator var = mAllVars.begin(); var != mAllVars.end(); ++var )
            {
                if( (*var)->rPosition() == i )
                {
                    if( !(*var)->getBasic() )
                    {
                        for( ExVariableMap::const_iterator iter = mExistingVars.begin(); iter != mExistingVars.end(); ++iter )
                        {
                            if( iter->second == *var )
                            {
                                stringstream out;
                                out << *(*iter).first;
                                _out << setw( maxlength ) << out.str();
                                break;
                            }
                        }
                    }
                }
            }
        }
        _out << endl;
        _out << setw( maxlength * (mColumnMaximum + 1) ) << setfill( '#' ) << "" << endl;
        _out << setfill( ' ' );
        for( vector<Variable*>::const_iterator var = mAllVars.begin(); var != mAllVars.end(); ++var )
        {
            if( (*var)->rPosition() == 0 )
            {
                if( (*var)->getBasic() )
                {
                    for( ExVariableMap::const_iterator iter = mExistingVars.begin(); iter != mExistingVars.end(); ++iter )
                    {
                        if( iter->second == *var )
                        {
                            stringstream out;
                            out << *(*iter).first;
                            _out << setw( maxlength ) << out.str() + " #";
                            break;
                        }
                    }
                }
            }
        }
        for( Tableau::const_iterator iter = mTableau.begin(); iter != mTableau.end(); ++iter )
        {
            if( (*iter).first.first > currentrow )
            {
                for( unsigned i = currentcolumn; i < mColumnMaximum; ++i )
                {
                    _out << setw( maxlength ) << "0";
                }
                _out << endl;
                ++currentrow;
                for( vector<Variable*>::const_iterator var = mAllVars.begin(); var != mAllVars.end(); ++var )
                {
                    if( (*var)->rPosition() == currentrow )
                    {
                        if( (*var)->getBasic() )
                        {
                            for( ExVariableMap::const_iterator iter = mExistingVars.begin(); iter != mExistingVars.end(); ++iter )
                            {
                                if( iter->second == *var )
                                {
                                    stringstream out;
                                    out << *(*iter).first;
                                    _out << setw( maxlength ) << out.str() + " #";
                                    break;
                                }
                            }
                        }
                    }
                }
                currentcolumn = 0;
            }
            while( currentcolumn < (*iter).first.second )
            {
                _out << setw( maxlength ) << "0";
                ++currentcolumn;
            }

            stringstream out;
            out << (*iter).second;
            _out << setw( maxlength ) << out.str();
            ++currentcolumn;
        }
        for( unsigned i = currentcolumn; i < mColumnMaximum; ++i )
        {
            _out << setw( maxlength ) << "0";
        }
        _out << endl;
        _out << setw( maxlength * (mColumnMaximum + 1) ) << setfill( frameSign ) << "" << endl;
    }

}    // namespace smtrat

