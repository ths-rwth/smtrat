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
/**
 * @file Formula.cpp
 *
 * @author Ulrich Loup
 * @author Florian Corzilius
 * @author Sebastian Junges
 * @since 2012-02-09
 * @version 2013-04-01
 */

//#define REMOVE_LESS_EQUAL_IN_CNF_TRANSFORMATION
//#define REMOVE_UNEQUAL_IN_CNF_TRANSFORMATION

#include "Formula.h"

using namespace std;

namespace smtrat
{
    ConstraintPool* Formula::mpConstraintPool = new ConstraintPool();

    Formula::Formula():
        mDeducted( false ),
        mPropositionsUptodate( false ),
        mActivity( 0 ),
        mDifficulty(0),
        mType( TTRUE ),
        mRealValuedVars(),
        mBooleanVars(),
        mpSubformulas( NULL ),
        mpFather( NULL ),
        mPropositions()
    {}

    Formula::Formula( const Type _type ):
        mDeducted( false ),
        mPropositionsUptodate( false ),
        mActivity( 0 ),
        mDifficulty( 0 ),
        mType( _type ),
        mRealValuedVars(),
        mBooleanVars(),
        mpSubformulas( (_type != TTRUE && _type != FFALSE) ? new list<Formula*>() : NULL ),
        mpFather( NULL ),
        mPropositions()
    {
        assert( _type != REALCONSTRAINT && _type != BOOL );
    }

    Formula::Formula( const string& _id ):
        mDeducted( false ),
        mPropositionsUptodate( false ),
        mActivity( 0 ),
        mDifficulty( 0 ),
        mType( BOOL ),
        mRealValuedVars(),
        mBooleanVars(),
        mpIdentifier( new string( _id )),
        mpFather( NULL ),
        mPropositions()
    {
        mBooleanVars.insert( _id );
    }

    Formula::Formula( const Constraint* _constraint ):
        mDeducted( false ),
        mPropositionsUptodate( false ),
        mActivity( 0 ),
        mDifficulty( 0 ),
        mType( REALCONSTRAINT ),
        mRealValuedVars( _constraint->variables() ),
        mBooleanVars(),
        mpConstraint( _constraint ),
        mpFather( NULL ),
        mPropositions()
    {}

    Formula::Formula( const Formula& _formula ):
        mDeducted( false ),
        mPropositionsUptodate( _formula.mPropositionsUptodate ),
        mActivity( _formula.mActivity ),
        mDifficulty( _formula.mDifficulty ),
        mType( _formula.getType() ),
        mRealValuedVars( _formula.realValuedVars() ),
        mBooleanVars( _formula.booleanVars() ),
        mpFather( NULL ),
        mPropositions(_formula.mPropositionsUptodate ? _formula.proposition(): Condition())
    {
        assert( &_formula != this );

        if( _formula.getType() == REALCONSTRAINT )
        {
            mpConstraint = _formula.pConstraint();
        }
        else if( isBooleanCombination() )
        {
            mpSubformulas = new list<Formula*>();
            for( const_iterator subFormula = _formula.subformulas().begin(); subFormula != _formula.subformulas().end(); ++subFormula )
            {
                addSubformula( new Formula( **subFormula ));
            }
        }
        else if( _formula.getType() == BOOL )
        {
            mpIdentifier = new string( _formula.identifier() );
        }
    }

    Formula::~Formula()
    {
        if( mType == BOOL )
        {
            delete mpIdentifier;
        }
        else if( mType != REALCONSTRAINT && mType != TTRUE && mType != FFALSE )
        {
            while( !mpSubformulas->empty() )
            {
                Formula* pSubForm = mpSubformulas->back();
                mpSubformulas->pop_back();
                delete pSubForm;
            }
            delete mpSubformulas;
        }
    }

    /**
     *
     * @return
     */
    Condition Formula::getPropositions()
    {
        if( !mPropositionsUptodate )
        {
            mPropositions = Condition();
            switch( mType )
            {
                case TTRUE:
                {
                    mPropositions |= STRONG_CONDITIONS;
                    break;
                }
                case FFALSE:
                {
                    mPropositions |= STRONG_CONDITIONS;
                    break;
                }
                case BOOL:
                {
                    mPropositions |= STRONG_CONDITIONS | PROP_CONTAINS_BOOLEAN;
                    break;
                }
                case REALCONSTRAINT:
                {
                    mPropositions |= STRONG_CONDITIONS;
                    addConstraintPropositions( *mpConstraint );
                    break;
                }
                case NOT:
                {
                    Condition subFormulaConds = (*mpSubformulas->begin())->getPropositions();
                    if( PROP_IS_AN_ATOM <= subFormulaConds )
                    {
                        mPropositions |= PROP_IS_A_CLAUSE | PROP_IS_A_LITERAL | PROP_IS_IN_CNF | PROP_IS_PURE_CONJUNCTION;
                    }
                    mPropositions |= (subFormulaConds & PROP_VARIABLE_DEGREE_LESS_THAN_THREE);
                    mPropositions |= (subFormulaConds & PROP_VARIABLE_DEGREE_LESS_THAN_FOUR);
                    mPropositions |= (subFormulaConds & PROP_VARIABLE_DEGREE_LESS_THAN_FIVE);
                    mPropositions |= (subFormulaConds & WEAK_CONDITIONS);
                    break;
                }
                case OR:
                {
                    mPropositions |= PROP_IS_A_CLAUSE | PROP_IS_IN_CNF | PROP_IS_IN_NNF;
                    mPropositions |= PROP_VARIABLE_DEGREE_LESS_THAN_THREE | PROP_VARIABLE_DEGREE_LESS_THAN_FOUR | PROP_VARIABLE_DEGREE_LESS_THAN_FIVE;
                    for( iterator subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
                    {
                        Condition subFormulaConds = (*subFormula)->getPropositions();
                        if( !(PROP_IS_A_LITERAL<=subFormulaConds) )
                        {
                            mPropositions &= ~PROP_IS_A_CLAUSE;
                            mPropositions &= ~PROP_IS_IN_CNF;
                        }
                        if( !(PROP_IS_IN_NNF<=subFormulaConds) )
                        {
                            mPropositions &= ~PROP_IS_IN_NNF;
                        }
                        mPropositions |= (subFormulaConds & WEAK_CONDITIONS);
                    }
                    break;
                }
                case AND:
                {
                    mPropositions |= PROP_IS_PURE_CONJUNCTION | PROP_IS_IN_CNF | PROP_IS_IN_NNF;
                    mPropositions |= PROP_VARIABLE_DEGREE_LESS_THAN_THREE | PROP_VARIABLE_DEGREE_LESS_THAN_FOUR | PROP_VARIABLE_DEGREE_LESS_THAN_FIVE;
                    for( iterator subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
                    {
                        Condition subFormulaConds = (*subFormula)->getPropositions();
                        if( !(PROP_IS_A_CLAUSE<=subFormulaConds) )
                        {
                            mPropositions &= ~PROP_IS_PURE_CONJUNCTION;
                            mPropositions &= ~PROP_IS_IN_CNF;
                        }
                        else if( !(PROP_IS_A_LITERAL<=subFormulaConds) )
                        {
                            mPropositions &= ~PROP_IS_PURE_CONJUNCTION;
                        }
                        if( !(PROP_IS_IN_NNF<=subFormulaConds) )
                        {
                            mPropositions &= ~PROP_IS_IN_NNF;
                        }
                        mPropositions |= (subFormulaConds & WEAK_CONDITIONS);
                    }
                    break;
                }
                case IMPLIES:
                {
                    mPropositions |= PROP_IS_IN_NNF;
                    mPropositions |= PROP_VARIABLE_DEGREE_LESS_THAN_THREE | PROP_VARIABLE_DEGREE_LESS_THAN_FOUR | PROP_VARIABLE_DEGREE_LESS_THAN_FIVE;
                    for( iterator subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
                    {
                        Condition subFormulaConds = (*subFormula)->getPropositions();
                        if( !(PROP_IS_IN_NNF<=subFormulaConds) )
                        {
                            mPropositions &= ~PROP_IS_IN_NNF;
                        }
                        mPropositions |= (subFormulaConds & WEAK_CONDITIONS);
                    }
                    break;
                }
                case IFF:
                {
                    mPropositions |= PROP_IS_IN_NNF;
                    mPropositions |= PROP_VARIABLE_DEGREE_LESS_THAN_THREE | PROP_VARIABLE_DEGREE_LESS_THAN_FOUR | PROP_VARIABLE_DEGREE_LESS_THAN_FIVE;
                    for( iterator subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
                    {
                        Condition subFormulaConds = (*subFormula)->getPropositions();
                        if( !(PROP_IS_IN_NNF<=subFormulaConds) )
                        {
                            mPropositions &= ~PROP_IS_IN_NNF;
                        }
                        mPropositions |= (subFormulaConds & WEAK_CONDITIONS);
                    }
                    break;
                }
                case XOR:
                {
                    mPropositions |= PROP_IS_IN_NNF;
                    mPropositions |= PROP_VARIABLE_DEGREE_LESS_THAN_THREE | PROP_VARIABLE_DEGREE_LESS_THAN_FOUR | PROP_VARIABLE_DEGREE_LESS_THAN_FIVE;
                    for( iterator subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
                    {
                        Condition subFormulaConds = (*subFormula)->getPropositions();
                        if( !(PROP_IS_IN_NNF<=subFormulaConds) )
                        {
                            mPropositions &= ~PROP_IS_IN_NNF;
                        }
                        mPropositions |= (subFormulaConds & WEAK_CONDITIONS);
                    }
                    break;
                }
                default:
                {
                    cerr << "Undefined operator!" << endl;
                    cerr << mType << endl;
                    cerr << *this << endl;
                    assert( false );
                }
            }
            mPropositionsUptodate = true;
        }
        return mPropositions;
    }

    /**
     *
     * @param _father
     */
    void Formula::setFather( Formula* _father )
    {
        assert( mpFather == NULL );
        mpFather = _father;
    }

    /**
     *
     * @param _formula
     */
    void Formula::addSubformula( Formula* _formula )
    {
        assert( isBooleanCombination() );
        assert( mType != NOT || mpSubformulas->empty() );
        _formula->setFather( this );

        /*
         * Add the variables of the formula to add to this formula.
         */
        mRealValuedVars.insert( _formula->realValuedVars().begin(), _formula->realValuedVars().end() );
        mBooleanVars.insert( _formula->booleanVars().begin(), _formula->booleanVars().end() );

        /*
         * Add the formula.
         */
        mpSubformulas->push_back( _formula );

        //Adapt the conditions, if they are up to date. (In this case very cheap)
        if( mPropositionsUptodate )
        {
            Condition condOfSubformula = _formula->getPropositions();
            if( mType == AND )
            {
                if( !(PROP_IS_A_LITERAL<=condOfSubformula) )
                {
                    mPropositions &= ~PROP_IS_PURE_CONJUNCTION;
                }
                else if( !(PROP_IS_A_CLAUSE<=condOfSubformula) )
                {
                    mPropositions &= ~PROP_IS_PURE_CONJUNCTION;
                    mPropositions &= ~PROP_IS_IN_CNF;
                }
            }
            else if( mType == OR )
            {
                if( !(PROP_IS_A_LITERAL<=condOfSubformula) )
                {
                    mPropositions &= ~PROP_IS_A_CLAUSE;
                }
            }
            if( !(PROP_IS_IN_NNF<=condOfSubformula) )
            {
                mPropositions &= ~PROP_IS_IN_NNF;
            }
            if( !(PROP_VARIABLE_DEGREE_LESS_THAN_FIVE<=condOfSubformula) )
            {
                mPropositions &= ~PROP_VARIABLE_DEGREE_LESS_THAN_THREE;
                mPropositions &= ~PROP_VARIABLE_DEGREE_LESS_THAN_FOUR;
                mPropositions &= ~PROP_VARIABLE_DEGREE_LESS_THAN_FIVE;
            }
            else if( !(PROP_VARIABLE_DEGREE_LESS_THAN_FOUR<=condOfSubformula) )
            {
                mPropositions &= ~PROP_VARIABLE_DEGREE_LESS_THAN_THREE;
                mPropositions &= ~PROP_VARIABLE_DEGREE_LESS_THAN_FOUR;
            }
            else if( !(PROP_VARIABLE_DEGREE_LESS_THAN_THREE<=condOfSubformula) )
            {
                mPropositions &= ~PROP_VARIABLE_DEGREE_LESS_THAN_THREE;
            }
            mPropositions |= (condOfSubformula & WEAK_CONDITIONS);
        }
    }

    /**
     *
     * @param _constraint
     */
    void Formula::addSubformula( const Constraint* _constraint )
    {
        assert( isBooleanCombination() );
        assert( mType != NOT || mpSubformulas->empty() );

        /*
         * Add the variables of the formula to add to this formula.
         */
        mRealValuedVars.insert( _constraint->variables().begin(), _constraint->variables().end() );

        /*
         * Add the formula consisting of this constraint.
         */
        Formula* form = new Formula( _constraint );
        form->setFather( this );
        mpSubformulas->push_back( form );

        //Adapt the conditions.
        if( mPropositionsUptodate )
        {
            mPropositions &= (form->getPropositions() | ~STRONG_CONDITIONS);
            mPropositions |= (form->getPropositions() & WEAK_CONDITIONS);
        }
    }

    /**
     *
     * @param _subformula
     * @return
     */
    Formula::iterator Formula::replace( Formula::iterator _toReplace, Formula* _replacement )
    {
        assert( isBooleanCombination() );
        assert( _toReplace != mpSubformulas->end() );
        Formula* pSubFormula = *_toReplace;
        Formula::iterator result = mpSubformulas->erase( _toReplace );
        delete pSubFormula;

        _replacement->setFather( this );
        /*
         * Add the variables of the formula to add to this formula.
         */
        mRealValuedVars.insert( _replacement->realValuedVars().begin(), _replacement->realValuedVars().end() );
        mBooleanVars.insert( _replacement->booleanVars().begin(), _replacement->booleanVars().end() );

        result = mpSubformulas->insert( result, _replacement );
        mPropositionsUptodate = false;
        return result;
    }

    /**
     *
     */
    void Formula::pop_back()
    {
        assert( isBooleanCombination() );
        Formula* pSubForm = mpSubformulas->back();
        mpSubformulas->pop_back();
        delete pSubForm;
        mPropositionsUptodate = false;
    }

    /**
     *
     */
    void Formula::pop_front()
    {
        assert( isBooleanCombination() );
        Formula* pSubForm = mpSubformulas->front();
        mpSubformulas->pop_front();
        delete pSubForm;
        mPropositionsUptodate = false;
    }

    /**
     *
     * @param _position
     */
    void Formula::erase( unsigned _position )
    {
        assert( isBooleanCombination() );
        assert( _position < mpSubformulas->size() );
        iterator subFormula = mpSubformulas->begin();
        unsigned pos        = 0;
        while( subFormula != mpSubformulas->end() )
        {
            if( pos == _position )
            {
                break;
            }
            ++subFormula;
            ++pos;
        }
        mpSubformulas->erase( subFormula );
    }

    /**
     *
     * @param _formula
     */
    void Formula::erase( const Formula* _formula )
    {
        assert( isBooleanCombination() );
        Formula::iterator subFormula = mpSubformulas->begin();
        while( subFormula != mpSubformulas->end() )
        {
            if( *subFormula == _formula )
            {
                break;
            }
            ++subFormula;
        }
        mpSubformulas->erase( subFormula );
    }

    /**
     *
     * @param _subformula
     * @return
     */
    Formula::iterator Formula::erase( Formula::iterator _subformula )
    {
        assert( isBooleanCombination() );
        assert( _subformula != mpSubformulas->end() );
        Formula* pSubFormula = *_subformula;
        Formula::iterator result = mpSubformulas->erase( _subformula );
        delete pSubFormula;
        mPropositionsUptodate = false;
        return result;
    }

    /**
     *
     * @return
     */
    Formula* Formula::pruneBack()
    {
        assert( isBooleanCombination() );
        assert( !mpSubformulas->empty() );
        Formula* result = mpSubformulas->back();
        result->resetFather();
        mpSubformulas->pop_back();
        mPropositionsUptodate = false;
        return result;
    }

    /**
     *
     * @return
     */
    Formula* Formula::pruneFront()
    {
        assert( isBooleanCombination() );
        assert( !mpSubformulas->empty() );
        Formula* result = mpSubformulas->front();
        result->resetFather();
        mpSubformulas->pop_front();
        mPropositionsUptodate = false;
        return result;
    }

    /**
     *
     * @param _position
     * @return
     */
    Formula* Formula::prune( unsigned _position )
    {
        assert( isBooleanCombination() );
        assert( _position < mpSubformulas->size() );
        iterator subFormula = mpSubformulas->begin();
        unsigned pos        = 0;
        while( subFormula != mpSubformulas->end() )
        {
            if( pos == _position )
            {
                Formula* pSubFormula = *subFormula;
                mpSubformulas->erase( subFormula );
                mPropositionsUptodate = false;
                return pSubFormula;
                break;
            }
            ++subFormula;
            ++pos;
        }
        return NULL;
    }

    /**
     *
     * @param _subformula
     * @return
     */
    Formula::iterator Formula::prune( Formula::iterator _subformula )
    {
        assert( isBooleanCombination() );
        assert( _subformula != mpSubformulas->end() );
        mPropositionsUptodate = false;
        return mpSubformulas->erase( _subformula );
    }

    /**
     *
     */
    void Formula::clear()
    {
        assert( isBooleanCombination() );
        while( !mpSubformulas->empty() )
        {
            Formula* pSubForm = mpSubformulas->back();
            mpSubformulas->pop_back();
            delete pSubForm;
        }
        mPropositionsUptodate = false;
    }

    /**
     *
     * @param _constraint
     */
    void Formula::addConstraintPropositions( const Constraint& _constraint )
    {
        switch( _constraint.maxMonomeDegree() )
        {
            case 0:
            {
                mPropositions |= PROP_CONTAINS_LINEAR_POLYNOMIAL;
                break;
            }
            case 1:
            {
                mPropositions |= PROP_CONTAINS_LINEAR_POLYNOMIAL;
                break;
            }
            case 2:
            {
                mPropositions |= PROP_CONTAINS_NONLINEAR_POLYNOMIAL;
                break;
            }
            case 3:
            {
                mPropositions |= PROP_CONTAINS_NONLINEAR_POLYNOMIAL;
                mPropositions &= ~PROP_VARIABLE_DEGREE_LESS_THAN_THREE;
                break;
            }
            case 4:
            {
                mPropositions |= PROP_CONTAINS_NONLINEAR_POLYNOMIAL;
                mPropositions &= ~PROP_VARIABLE_DEGREE_LESS_THAN_FOUR;
                break;
            }
            case 5:
            {
                mPropositions |= PROP_CONTAINS_NONLINEAR_POLYNOMIAL;
                mPropositions &= ~PROP_VARIABLE_DEGREE_LESS_THAN_FIVE;
                break;
            }
            default:
            {
            }
        }
        switch( _constraint.relation() )
        {
            case CR_EQ:
            {
                mPropositions |= PROP_CONTAINS_EQUATION;
                break;
            }
            case CR_NEQ:
            {
                mPropositions |= PROP_CONTAINS_STRICT_INEQUALITY;
                break;
            }
            case CR_LEQ:
            {
                mPropositions |= PROP_CONTAINS_INEQUALITY;
                break;
            }
            case CR_GEQ:
            {
                mPropositions |= PROP_CONTAINS_INEQUALITY;
                break;
            }
            case CR_LESS:
            {
                mPropositions |= PROP_CONTAINS_STRICT_INEQUALITY;
                break;
            }
            case CR_GREATER:
            {
                mPropositions |= PROP_CONTAINS_STRICT_INEQUALITY;
                break;
            }
            default:
            {
            }
        }
        if( _constraint.containsIntegerValuedVariable() )
        {
            mPropositions |= PROP_CONTAINS_INTEGER_VALUED_VARS;
        }
        if( _constraint.containsRealValuedVariable() )
        {
            mPropositions |= PROP_CONTAINS_REAL_VALUED_VARS;
        }
    }

    /**
     *
     * @param _const
     */
    void Formula::getConstraints( vector<const Constraint*>& _const ) const
    {
        if( mType == REALCONSTRAINT )
        {
            _const.push_back( mpConstraint );
        }
        else if( mType == AND || mType == OR || mType == NOT || mType == IFF || mType == XOR || mType == IMPLIES )
        {
            for( const_iterator subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
            {
                (*subFormula)->getConstraints( _const );
            }
        }
    }

    /**
     *
     * @param _formula
     * @param _keepConstraints
     */
    void Formula::toCNF( Formula& _formula, bool _keepConstraints )
    {
        if( _keepConstraints && (_formula.getPropositions() | ~PROP_IS_IN_CNF) == ~PROP_TRUE )
        {
            return;
        }
        else if( _formula.getType() == NOT && (_formula.getPropositions() | ~PROP_IS_IN_CNF) == ~PROP_TRUE )
        {
            resolveNegation( _formula, _keepConstraints );
            return;
        }
        else if( _formula.isAtom() )
        {
            return;
        }
        Formula* copy = new Formula( _formula.getType() );
        while( !_formula.empty() )
        {
            copy->addSubformula( _formula.pruneFront() );
        }
        _formula.copyAndDelete( new Formula( AND ));
        vector<Formula*> subformulasToTransform = vector<Formula*>();
        subformulasToTransform.push_back( copy );
        while( !subformulasToTransform.empty() )
        {
            Formula* currentFormula = subformulasToTransform.back();
            subformulasToTransform.pop_back();
            switch( currentFormula->getType() )
            {
                case BOOL:
                {
                    _formula.addSubformula( currentFormula );
                    break;
                }
                case REALCONSTRAINT:
                {
                    #ifdef REMOVE_LESS_EQUAL_IN_CNF_TRANSFORMATION
                    const Constraint* constraint = currentFormula->pConstraint();
                    if( constraint->relation() == CR_LEQ )
                    {
                        Formula* newFormula = new Formula( OR );
                        newFormula->addSubformula( new Formula( Formula::newConstraint( constraint->lhs(), CR_LESS, constraint->variables() ) ) );
                        newFormula->addSubformula( new Formula( Formula::newConstraint( constraint->lhs(), CR_EQ, constraint->variables() )));
                        delete currentFormula;
                        subformulasToTransform.push_back( newFormula );
                    }
                    else
                    {
                        _formula.addSubformula( currentFormula );
                    }
                    #else
                    _formula.addSubformula( currentFormula );
                    #endif
                    break;
                }
                case TTRUE:
                {
                    /*
                     * Remove it.
                     */
                    delete currentFormula;
                    break;
                }
                case FFALSE:
                {
                    /*
                     * Makes everything false.
                     */
                    while( !_formula.empty() )
                    {
                        Formula* formulaToDelete = _formula.pruneBack();
                        delete formulaToDelete;
                    }
                    while( !subformulasToTransform.empty() )
                    {
                        Formula* formulaToDelete = subformulasToTransform.back();
                        subformulasToTransform.pop_back();
                        delete formulaToDelete;
                    }
                    _formula.copyAndDelete( currentFormula );
                    return;
                }
                case NOT:
                {
                    /*
                     * Try to resolve this negation.
                     */
                    if( !Formula::resolveNegation( *currentFormula, _keepConstraints ))
                    {
                        /*
                         * It is a literal.
                         */
                        _formula.addSubformula( currentFormula );
                    }
                    else
                    {
                        subformulasToTransform.push_back( currentFormula );
                    }
                    break;
                }
                case AND:
                {
                    /*
                     * (and phi_1 .. phi_n) -> psi_1 .. psi_m
                     */
                    while( !currentFormula->empty() )
                    {
                        subformulasToTransform.push_back( currentFormula->pruneBack() );
                    }
                    delete currentFormula;
                    break;
                }
                // Note, that the following case could be implemented using less code, but it would clearly
                // lead to a worse performance as we would then not benefit from the properties of a disjunction.
                case OR:
                {
                    /*
                     * (or phi_1 .. phi_n) -> (or psi_1 .. psi_m)
                     *
                     * where phi_i is transformed as follows:
                     */
                    vector<Formula*> phis = vector<Formula*>();
                    while( !currentFormula->empty() )
                    {
                        phis.push_back( currentFormula->pruneBack() );
                    }
                    while( !phis.empty() )
                    {
                        Formula* currentSubformula = phis.back();
                        phis.pop_back();
                        switch( currentSubformula->getType() )
                        {
                            // B -> B
                            case BOOL:
                            {
                                currentFormula->addSubformula( currentSubformula );
                                break;
                            }
                            // p~0 -> p~0
                            case REALCONSTRAINT:
                            {
                                #ifdef REMOVE_LESS_EQUAL_IN_CNF_TRANSFORMATION
                                const Constraint* constraint = currentSubformula->pConstraint();
                                if( constraint->relation() == CR_LEQ )
                                {
                                    Formula* newFormula = new Formula( OR );
                                    newFormula->addSubformula( new Formula( Formula::newConstraint( constraint->lhs(), CR_LESS, constraint->variables() ) ) );
                                    newFormula->addSubformula( new Formula( Formula::newConstraint( constraint->lhs(), CR_EQ, constraint->variables() )));
                                    delete currentSubformula;
                                    phis.push_back( newFormula );
                                }
                                else
                                {
                                    currentFormula->addSubformula( currentSubformula );
                                }
                                #else
                                currentFormula->addSubformula( currentSubformula );
                                #endif
                                break;
                            }
                            // remove the entire considered disjunction and everything which has been created by considering it
                            case TTRUE:
                            {
                                while( !currentFormula->empty() )
                                {
                                    Formula* formulaToDelete = currentFormula->pruneBack();
                                    delete formulaToDelete;
                                }
                                while( !phis.empty() )
                                {
                                    Formula* formulaToDelete = phis.back();
                                    phis.pop_back();
                                    delete formulaToDelete;
                                }
                                delete currentSubformula;
                                break;
                            }
                            // remove it
                            case FFALSE:
                            {
                                delete currentSubformula;
                                break;
                            }
                            // resolve the negation
                            case NOT:
                            {
                                /*
                                 * Try to resolve this negation.
                                 */
                                if( Formula::resolveNegation( *currentSubformula, _keepConstraints ))
                                {
                                    phis.push_back( currentSubformula );
                                }
                                else
                                {
                                    /*
                                     * It is a literal.
                                     */
                                    currentFormula->addSubformula( currentSubformula );
                                }
                                break;
                            }
                            // (and phi_i1 .. phi_ik) -> h_i, where (or (not h_i) phi_i1) .. (or (not h_i) phi_ik) is added to the queue
                            case AND:
                            {
                                Formula* hi = new Formula( Formula::newAuxiliaryBooleanVariable() );
                                hi->setDifficulty(currentSubformula->difficulty());
                                while( !currentSubformula->empty() )
                                {
                                    Formula* formulaToAssert = new Formula( OR );
                                    formulaToAssert->addSubformula( new Formula( NOT ));
                                    formulaToAssert->back()->addSubformula( new Formula( *hi ));
                                    formulaToAssert->addSubformula( currentSubformula->pruneBack() );
                                    subformulasToTransform.push_back( formulaToAssert );
                                }
                                delete currentSubformula;
                                currentFormula->addSubformula( hi );
                                break;
                            }
                            // (or phi_i1 .. phi_ik) -> phi_i1 .. phi_ik
                            case OR:
                            {
                                while( !currentSubformula->empty() )
                                {
                                    phis.push_back( currentSubformula->pruneBack() );
                                }
                                delete currentSubformula;
                                break;
                            }
                            // (-> lhs_i rhs_i) -> (not lhs_i) rhs_i
                            case IMPLIES:
                            {
                                assert( currentSubformula->size() == 2 );
                                Formula* rhs = currentSubformula->pruneBack();
                                Formula* lhs = currentSubformula->pruneBack();
                                delete currentSubformula;
                                phis.push_back( new Formula( NOT ));
                                phis.back()->addSubformula( lhs );
                                phis.push_back( rhs );
                                break;
                            }
                            // (iff lhs_i rhs_i) -> h_i1 h_i2, where (or (not h_i1) lhs_i) (or (not h_i1) rhs_i)
                            //                                       (or (not h_i2) (not lhs_i)) (or (not h_i2) (not rhs_i))  is added to the queue
                            case IFF:
                            {
                                assert( currentSubformula->size() == 2 );
                                Formula* h_i1  = new Formula( Formula::newAuxiliaryBooleanVariable() );
                                Formula* h_i2  = new Formula( Formula::newAuxiliaryBooleanVariable() );
                                Formula* rhs_i = currentSubformula->pruneBack();
                                Formula* lhs_i = currentSubformula->pruneBack();
                                delete currentSubformula;

                                subformulasToTransform.push_back( new Formula( OR ));
                                subformulasToTransform.back()->addSubformula( new Formula( NOT ));
                                subformulasToTransform.back()->back()->addSubformula( new Formula( *h_i1 ));
                                subformulasToTransform.back()->addSubformula( lhs_i );
                                subformulasToTransform.push_back( new Formula( OR ));
                                subformulasToTransform.back()->addSubformula( new Formula( NOT ));
                                subformulasToTransform.back()->back()->addSubformula( new Formula( *h_i1 ));
                                subformulasToTransform.back()->addSubformula( rhs_i );
                                subformulasToTransform.push_back( new Formula( OR ));
                                subformulasToTransform.back()->addSubformula( new Formula( NOT ));
                                subformulasToTransform.back()->back()->addSubformula( new Formula( *h_i2 ));
                                subformulasToTransform.back()->addSubformula( new Formula( NOT ));
                                subformulasToTransform.back()->back()->addSubformula( new Formula( *lhs_i ));
                                subformulasToTransform.push_back( new Formula( OR ));
                                subformulasToTransform.back()->addSubformula( new Formula( NOT ));
                                subformulasToTransform.back()->back()->addSubformula( new Formula( *h_i2 ));
                                subformulasToTransform.back()->addSubformula( new Formula( NOT ));
                                subformulasToTransform.back()->back()->addSubformula( new Formula( *rhs_i ));

                                currentFormula->addSubformula( h_i1 );
                                currentFormula->addSubformula( h_i2 );
                                break;
                            }
                            // (xor lhs_i rhs_i) -> h_i1 h_i2, where (or (not h_i1) (not lhs_i)) (or (not h_i1) rhs_i)
                            //                                       (or (not h_i2) lhs_i) (or (not h_i2) (not rhs_i))  is added to the queue
                            case XOR:
                            {
                                assert( currentSubformula->size() == 2 );
                                Formula* h_i1  = new Formula( Formula::newAuxiliaryBooleanVariable() );
                                Formula* h_i2  = new Formula( Formula::newAuxiliaryBooleanVariable() );
                                Formula* rhs_i = currentSubformula->pruneBack();
                                Formula* lhs_i = currentSubformula->pruneBack();
                                delete currentSubformula;

                                subformulasToTransform.push_back( new Formula( OR ));
                                subformulasToTransform.back()->addSubformula( new Formula( NOT ));
                                subformulasToTransform.back()->back()->addSubformula( new Formula( *h_i1 ));
                                subformulasToTransform.back()->addSubformula( new Formula( NOT ));
                                subformulasToTransform.back()->back()->addSubformula( lhs_i );
                                subformulasToTransform.push_back( new Formula( OR ));
                                subformulasToTransform.back()->addSubformula( new Formula( NOT ));
                                subformulasToTransform.back()->back()->addSubformula( new Formula( *h_i1 ));
                                subformulasToTransform.back()->addSubformula( rhs_i );
                                subformulasToTransform.push_back( new Formula( OR ));
                                subformulasToTransform.back()->addSubformula( new Formula( NOT ));
                                subformulasToTransform.back()->back()->addSubformula( new Formula( *h_i2 ));
                                subformulasToTransform.back()->addSubformula( new Formula( *lhs_i ));
                                subformulasToTransform.push_back( new Formula( OR ));
                                subformulasToTransform.back()->addSubformula( new Formula( NOT ));
                                subformulasToTransform.back()->back()->addSubformula( new Formula( *h_i2 ));
                                subformulasToTransform.back()->addSubformula( new Formula( NOT ));
                                subformulasToTransform.back()->back()->addSubformula( new Formula( *rhs_i ));

                                currentFormula->addSubformula( h_i1 );
                                currentFormula->addSubformula( h_i2 );
                                break;
                            }
                            default:
                            {
                                cerr << "Unexpected type of formula!" << endl;
                                assert( false );
                            }
                        }
                    }
                    if( currentFormula->isBooleanCombination() && currentFormula->size() == 1 )
                    {
                        _formula.addSubformula( currentFormula->pruneBack() );
                        delete currentFormula;
                    }
                    else if( !currentFormula->empty() )
                        _formula.addSubformula( currentFormula );
                    else
                    {
                        delete currentFormula;
                    }
                    break;
                }
                case IMPLIES:
                {
                    /*
                    * (-> lhs rhs)  ->  (or (not lhs) rhs)
                    */
                    assert( currentFormula->size() == 2 );
                    Formula* rhs = currentFormula->pruneBack();
                    Formula* lhs = currentFormula->pruneBack();
                    assert( currentFormula->cpFather() == NULL );
                    delete currentFormula;
                    Formula* newFormula = new Formula( OR );
                    newFormula->addSubformula( new Formula( NOT ));
                    newFormula->back()->addSubformula( lhs );
                    newFormula->addSubformula( rhs );
                    subformulasToTransform.push_back( newFormula );
                    break;
                }
                case IFF:
                {
                    /*
                    * (iff lhs rhs)  ->  (or h1 h2) (or (not h1) lhs) (or (not h1) rhs) (or (not h2) (not lhs)) (or (not h2) (not rhs))
                    */
                    assert( currentFormula->size() == 2 );
                    // Get lhs and rhs and delete currentFormula.
                    Formula* rhs = currentFormula->pruneBack();
                    Formula* lhs = currentFormula->pruneBack();
                    delete currentFormula;
                    // Add (or h1 h2) to the passed formula, where h1 and h2 are fresh Boolean variables.
                    Formula* h1     = new Formula( Formula::newAuxiliaryBooleanVariable() );
                    Formula* h2     = new Formula( Formula::newAuxiliaryBooleanVariable() );
                    Formula* clause = new Formula( OR );
                    clause->addSubformula( h1 );
                    clause->addSubformula( h2 );
                    _formula.addSubformula( clause );
                    // Append (or (not h1) lhs), (or (not h1) rhs), (or (not h2) (not lhs)) and (or (not h2) (not rhs)) to _formulasToAssert.
                    Formula* formulaToAssertA = new Formula( OR );
                    formulaToAssertA->addSubformula( new Formula( NOT ));
                    formulaToAssertA->back()->addSubformula( new Formula( *h1 ));
                    formulaToAssertA->addSubformula( lhs );    // Once it can be used, otherwise copy it,
                    subformulasToTransform.push_back( formulaToAssertA );
                    Formula* formulaToAssertB = new Formula( OR );
                    formulaToAssertB->addSubformula( new Formula( NOT ));
                    formulaToAssertB->back()->addSubformula( new Formula( *h1 ));
                    formulaToAssertB->addSubformula( rhs );    // Once it can be used, otherwise copy it,
                    subformulasToTransform.push_back( formulaToAssertB );
                    Formula* formulaToAssertC = new Formula( OR );
                    formulaToAssertC->addSubformula( new Formula( NOT ));
                    formulaToAssertC->back()->addSubformula( new Formula( *h2 ));
                    formulaToAssertC->addSubformula( new Formula( NOT ));
                    formulaToAssertC->back()->addSubformula( new Formula( *lhs ));
                    subformulasToTransform.push_back( formulaToAssertC );
                    Formula* formulaToAssertD = new Formula( OR );
                    formulaToAssertD->addSubformula( new Formula( NOT ));
                    formulaToAssertD->back()->addSubformula( new Formula( *h2 ));
                    formulaToAssertD->addSubformula( new Formula( NOT ));
                    formulaToAssertD->back()->addSubformula( new Formula( *rhs ));
                    subformulasToTransform.push_back( formulaToAssertD );
                    break;
                }
                case XOR:
                {
                    /*
                    * (xor lhs rhs)  ->  (or h1 h2) (or (not h1) (not lhs)) (or (not h1) rhs) (or (not h2) lhs) (or (not h2) (not rhs))
                    */
                    assert( currentFormula->size() == 2 );
                    // Get lhs and rhs and delete currentFormula.
                    Formula* rhs = currentFormula->pruneBack();
                    Formula* lhs = currentFormula->pruneBack();
                    delete currentFormula;
                    // Add (or h1 h2) to the passed formula, where h1 and h2 are fresh Boolean variables.
                    Formula* h1     = new Formula( Formula::newAuxiliaryBooleanVariable() );
                    Formula* h2     = new Formula( Formula::newAuxiliaryBooleanVariable() );
                    Formula* clause = new Formula( OR );
                    clause->addSubformula( h1 );
                    clause->addSubformula( h2 );
                    _formula.addSubformula( clause );
                    // Append (or (not h1) (not lhs)), (or (not h1) rhs), (or (not h2) lhs) and (or (not h2) (not rhs)) to _formulasToAssert.
                    Formula* formulaToAssertA = new Formula( OR );
                    formulaToAssertA->addSubformula( new Formula( NOT ));
                    formulaToAssertA->back()->addSubformula( new Formula( *h1 ));
                    formulaToAssertA->addSubformula( new Formula( NOT ));
                    formulaToAssertA->back()->addSubformula( lhs );    // Once it can be used, otherwise copy it,
                    subformulasToTransform.push_back( formulaToAssertA );
                    Formula* formulaToAssertB = new Formula( OR );
                    formulaToAssertB->addSubformula( new Formula( NOT ));
                    formulaToAssertB->back()->addSubformula( new Formula( *h1 ));
                    formulaToAssertB->addSubformula( rhs );    // Once it can be used, otherwise copy it,
                    subformulasToTransform.push_back( formulaToAssertB );
                    Formula* formulaToAssertC = new Formula( OR );
                    formulaToAssertC->addSubformula( new Formula( NOT ));
                    formulaToAssertC->back()->addSubformula( new Formula( *h2 ));
                    formulaToAssertC->addSubformula( new Formula( *lhs ));
                    subformulasToTransform.push_back( formulaToAssertC );
                    Formula* formulaToAssertD = new Formula( OR );
                    formulaToAssertD->addSubformula( new Formula( NOT ));
                    formulaToAssertD->back()->addSubformula( new Formula( *h2 ));
                    formulaToAssertD->addSubformula( new Formula( NOT ));
                    formulaToAssertD->back()->addSubformula( new Formula( *rhs ));
                    subformulasToTransform.push_back( formulaToAssertD );
                    break;
                }
                default:
                {
                    cerr << "Unexpected type of formula!" << endl;
                    assert( false );
                }
            }
        }
        if( _formula.empty() )
        {
            _formula.copyAndDelete( new Formula( TTRUE ));
        }
        else if( _formula.isBooleanCombination() && _formula.size() == 1 )
        {
            Formula* subFormula = _formula.pruneBack();
            _formula.copyAndDelete( subFormula );
        }
        _formula.getPropositions();

    }

    /**
     *
     * @param _formula
     * @param _keepConstraints
     */
    bool Formula::resolveNegation( Formula& _formula, bool _keepConstraint )
    {
        assert( _formula.getType() == NOT );
        Formula* subformula = _formula.back();
        switch( subformula->getType() )
        {
            case BOOL:
            {
                return false;
            }
            case REALCONSTRAINT:
            {
                if( _keepConstraint )
                {
                    return false;
                }
                else
                {
                    const Constraint* constraint = subformula->pConstraint();
                    _formula.pop_back();
                    switch( constraint->relation() )
                    {
                        case CR_EQ:
                        {
                            #ifdef REMOVE_UNEQUAL_IN_CNF_TRANSFORMATION
                            _formula.copyAndDelete( new Formula( OR ));
                            _formula.addSubformula( new Formula( Formula::newConstraint( constraint->lhs(), CR_LESS, constraint->variables() )));
                            _formula.addSubformula( new Formula( Formula::newConstraint( -constraint->lhs(), CR_LESS, constraint->variables() )));
                            #else
                            _formula.copyAndDelete( new Formula( Formula::newConstraint( constraint->lhs(), CR_NEQ, constraint->variables() )));
                            #endif
                            return true;
                        }
                        case CR_LEQ:
                        {
                            _formula.copyAndDelete( new Formula( Formula::newConstraint( -constraint->lhs(), CR_LESS, constraint->variables() )));
                            return false;
                        }
                        case CR_LESS:
                        {
                            #ifdef REMOVE_LESS_EQUAL_IN_CNF_TRANSFORMATION
                            _formula.copyAndDelete( new Formula( OR ));
                            _formula.addSubformula( new Formula( Formula::newConstraint( -constraint->lhs(), CR_LESS, constraint->variables() )));
                            _formula.addSubformula( new Formula( Formula::newConstraint( -constraint->lhs(), CR_EQ, constraint->variables() )));
                            return true;
                            #else
                            _formula.copyAndDelete( new Formula( Formula::newConstraint( -constraint->lhs(), CR_LEQ, constraint->variables() )));
                            return false;
                            #endif
                        }
                        case CR_NEQ:
                        {
                            _formula.copyAndDelete( new Formula( Formula::newConstraint( constraint->lhs(), CR_EQ, constraint->variables() )));
                            return false;
                        }
                        default:
                        {
                            cerr << "Unexpected relation symbol!" << endl;
                            assert( false );
                            return false;
                        }
                    }
                }
            }
            case TTRUE:
            {
                /*
                 * (not true)  ->  false
                 */
                _formula.pop_back();
                _formula.copyAndDelete( new Formula( FFALSE ) );
                return true;
            }
            case FFALSE:
            {
                /*
                 * (not false)  ->  true
                 */
                _formula.pop_back();
                _formula.copyAndDelete( new Formula( TTRUE ) );
                return true;
            }
            case NOT:
            {
                /*
                 * (not (not phi))  ->  phi
                 */
                Formula* subsubformula = subformula->pruneBack();
                _formula.pop_back();
                _formula.copyAndDelete( subsubformula );
                return true;
            }
            case AND:
            {
                /*
                 * (not (and phi_1 .. phi_n))  ->  (or (not phi_1) .. (not phi_n))
                 */
                vector<Formula*> subsubformulas = vector<Formula*>();
                while( !subformula->empty() )
                {
                    subsubformulas.push_back( subformula->pruneBack() );
                }
                _formula.pop_back();
                _formula.copyAndDelete( new Formula( OR ));
                while( !subsubformulas.empty() )
                {
                    _formula.addSubformula( new Formula( NOT ));
                    _formula.back()->addSubformula( subsubformulas.back() );
                    subsubformulas.pop_back();
                }
                return true;
            }
            case OR:
            {
                /*
                 * (not (or phi_1 .. phi_n))  ->  (and (not phi_1) .. (not phi_n))
                 */
                vector<Formula*> subsubformulas = vector<Formula*>();
                while( !subformula->empty() )
                {
                    subsubformulas.push_back( subformula->pruneBack() );
                }
                _formula.pop_back();
                _formula.copyAndDelete( new Formula( AND ));
                while( !subsubformulas.empty() )
                {
                    _formula.addSubformula( new Formula( NOT ));
                    _formula.back()->addSubformula( subsubformulas.back() );
                    subsubformulas.pop_back();
                }
                return true;
            }
            case IMPLIES:
            {
                assert( subformula->size() == 2 );

                /*
                 * (not (implies lhs rhs))  ->  (and lhs (not rhs))
                 */
                Formula* rhsOfSubformula = subformula->pruneBack();
                Formula* lhsOfSubformula = subformula->pruneBack();
                _formula.pop_back();
                _formula.copyAndDelete( new Formula( AND ));
                _formula.addSubformula( lhsOfSubformula );
                _formula.addSubformula( new Formula( NOT ));
                _formula.back()->addSubformula( rhsOfSubformula );
                return true;
            }
            case IFF:
            {
                assert( subformula->size() == 2 );

                /*
                 * (not (iff lhs rhs))  ->  (xor lhs rhs)
                 */
                Formula* rhsOfSubformula = subformula->pruneBack();
                Formula* lhsOfSubformula = subformula->pruneBack();
                _formula.pop_back();
                _formula.copyAndDelete( new Formula( XOR ));
                _formula.addSubformula( lhsOfSubformula );
                _formula.addSubformula( rhsOfSubformula );
                return true;
            }
            case XOR:
            {
                assert( subformula->size() == 2 );

                /*
                 * (not (xor lhs rhs))  ->  (iff lhs rhs)
                 */
                Formula* rhsOfSubformula = subformula->pruneBack();
                Formula* lhsOfSubformula = subformula->pruneBack();
                _formula.pop_back();
                _formula.copyAndDelete( new Formula( IFF ));
                _formula.addSubformula( lhsOfSubformula );
                _formula.addSubformula( rhsOfSubformula );
                return true;
            }
            default:
            {
                cerr << "Unexpected type of formula!" << endl;
                assert( false );
                return false;
            }
        }
        _formula.getPropositions();
    }

    /**
     *
     * @param _out
     * @param _init
     * @param _onOneLine
     */
    void Formula::print( ostream& _out, const string _init, bool _smtlib, bool _onOneLine ) const
    {
        string oper = "";
        switch( mType )
        {
            case AND:
            {
                oper = "and";
                break;
            }
            case OR:
            {
                oper = "or";
                break;
            }
            case NOT:
            {
                oper = "not";
                break;
            }
            case IFF:
            {
                oper = "=";
                break;
            }
            case XOR:
            {
                oper = "xor";
                break;
            }
            case IMPLIES:
            {
                oper = "=>";
                break;
            }
            case BOOL:
            {
                _out << _init << *mpIdentifier;
                break;
            }
            case REALCONSTRAINT:
            {
                _out << _init;
                if( _smtlib )
                {
                    _out << mpConstraint->smtlibString();
                }
                else
                {
                    mpConstraint->print( _out );
                    _out << " (" << mDifficulty << ":" << mActivity << ")";
                }
                break;
            }
            case TTRUE:
            {
                _out << _init << "true";
                break;
            }
            case FFALSE:
            {
                _out << _init << "false";
                break;
            }
            default:
            {
                _out << _init << "undefined";
            }
        }
        if( !oper.empty() )
        {
            _out << _init << "(" << oper;
            if( _onOneLine )
            {
                _out << " ";
            }
            else
            {
                _out << endl;
            }
            std::list<Formula*>::const_iterator subFormula = mpSubformulas->begin();
            while( subFormula != mpSubformulas->end() )
            {
                assert( (*subFormula)->cpFather() == this );
                if( _onOneLine )
                {
                    (*subFormula)->print( _out, "", _smtlib, _onOneLine );
                    _out << " ";
                }
                else
                {
                    (*subFormula)->print( _out, _init + "   ", _smtlib, _onOneLine );
                    _out << endl;
                }
                ++subFormula;
            }
            _out << _init << ")";
        }
    }

    /**
     *
     * @param _out
     * @param _init
     */
    void Formula::printProposition( ostream& _out, const string _init ) const
    {
        _out << _init;
        for( unsigned i = 0; i < proposition().size(); ++i )
        {
            if( fmod( i, 10.0 ) == 0.0 ) _out << " ";
            _out << proposition()[i];
        }
        _out << endl;
    }

    /**
     *
     * @param _ostream
     * @param _formula
     * @return
     */
    ostream& operator <<( ostream& _ostream, const Formula& _formula )
    {
        _formula.print( _ostream, "", true );
        return _ostream;
    }

    /**
     *
     * @param _infix
     * @return
     */
    string Formula::toString( bool _infix ) const
    {
        string result = "";
        switch( mType )
        {
            case AND:
            {
                result += "(and";
                break;
            }
            case OR:
            {
                result += "(or";
                break;
            }
            case NOT:
            {
                result += "(not";
                break;
            }
            case IFF:
            {
                result += "(=";
                break;
            }
            case XOR:
            {
                result += "(xor";
                break;
            }
            case IMPLIES:
            {
                result += "(=>";
                break;
            }
            case BOOL:
            {
                result += *mpIdentifier;
                break;
            }
            case REALCONSTRAINT:
            {
                if( _infix )
                {
                    result += "( " + mpConstraint->toString() + " )";
                }
                else
                {
                    result += mpConstraint->smtlibString();
                }
                break;
            }
            case TTRUE:
            {
                result += "true";
                break;
            }
            case FFALSE:
            {
                result += "false";
                break;
            }
            default:
            {
                result += "undefined";
            }
        }
        if( isBooleanCombination() )
        {
            for( std::list<Formula*>::const_iterator subformula = mpSubformulas->begin(); subformula != mpSubformulas->end(); ++subformula )
                result += " " + (*subformula)->toString( _infix );
            result += ")";
        }
        return result;
    }

    /**
     *
     * @param type
     * @return
     */
    std::string Formula::FormulaTypeToString( Type type )
    {
        string oper = "";
        switch( type )
        {
            case AND:
            {
                oper = "and";
                break;
            }
            case OR:
            {
                oper = "or";
                break;
            }
            case NOT:
            {
                oper = "not";
                break;
            }
            case IFF:
            {
                oper = "=";
                break;
            }
            case XOR:
            {
                oper = "xor";
                break;
            }
            case IMPLIES:
            {
                oper = "=>";
                break;
            }
            case TTRUE:
            {
                oper = "true";
                break;
            }
            case FFALSE:
            {
                oper = "false";
                break;
            }
            default:
            {
                oper = "";
            }
        }
        return oper;
    }

    void Formula::renameVariables()
    {
//        const GiNaC::symtab&               realValuedVars = input.first->realValuedVars();
//        const std::set< std::string >&        booleanVars = input.first->booleanVars();
        unsigned                                        x = 0; // real variable counter
        unsigned                                        y = 0; // Boolean variable counter
        GiNaC::symtab::iterator                   i = mRealValuedVars.begin();
        std::set< std::string >::iterator         j = mBooleanVars.begin();
        if( i != mRealValuedVars.end() )
        {
            for( ; i != mRealValuedVars.end(); ++i )
            {
                std::stringstream xStr;
                xStr << "r" << x;
                ++x;
//                i->first = xStr.str();
//                GiNaC::ex_to<GiNaC::symbol>( i->second ).set_name( xStr.str() );
//                variableIds[ i->first ] = "r" + xStr.str();
//                cout << "Mapping " << i->first << " -> " << variableIds[ i->first ] << endl;
            }
        }
        else if( j != mBooleanVars.end() )
        {
            for( ; j != mBooleanVars.end(); ++j )
            {
                std::stringstream yStr;
                yStr << "b" << y;
                ++y;
//                *j = yStr.str();
//                variableIds[ *j ] = "b" + yStr.str();
            }
        }
    }

    /**
     *
     * @param seperator
     * @return
     */
    std::string Formula::variableListToString( std::string seperator, const unordered_map<string, string>& variableIds ) const
    {
        GiNaC::symtab::const_iterator                   i = mRealValuedVars.begin();
        std::set< std::string, strCmp >::const_iterator j = mBooleanVars.begin();
        string                                     result = "";
        if( i != mRealValuedVars.end() )
        {
            unordered_map<string, string>::const_iterator vId = variableIds.find(i->first);
            result += vId == variableIds.end() ? i->first : vId->second;
            for( ++i; i != mRealValuedVars.end(); ++i )
            {
                result += seperator;
                vId = variableIds.find(i->first);
                result += vId == variableIds.end() ? i->first : vId->second;
            }
        }
        else if( j != mBooleanVars.end() )
        {
            unordered_map<string, string>::const_iterator vId = variableIds.find(*j);
            result += vId == variableIds.end() ? *j : vId->second;
            for( ++j; j != mBooleanVars.end(); ++j )
            {
                result += seperator;
                vId = variableIds.find(*j);
                result += vId == variableIds.end() ? *j : vId->second;
            }
        }
        return result;
    }

    /**
     * Generates a string displaying the formula as a redlog formula.
     * @return
     */
    std::string Formula::toRedlogFormat( bool withVariables ) const
    {
        string result = "";
        string oper = Formula::FormulaTypeToString( mType );
        switch( mType )
        {
            // unary cases
            case TTRUE:
            {
                result += " " + oper + " ";
                break;
            }
            case FFALSE:
            {
                result += " " + oper + " ";
                break;
            }
            case NOT:
            {
                result += " " + oper + "( " + (*mpSubformulas->begin())->toRedlogFormat( withVariables ) + " )";
                break;
            }
            case REALCONSTRAINT:
            {
                result += constraint().toString();
                break;
            }
            case BOOL:
            {
                result += *mpIdentifier + " = 1";
                break;
            }
            default:
            {
                // recursive print of the subformulas
                if( withVariables )
                { // add the variables
                    result += "( ex( {";
                    result += variableListToString( "," );
                    result += "}, (";
                    // Make pseudo Booleans.
                    for( std::set< std::string, strCmp >::const_iterator j = mBooleanVars.begin(); j != mBooleanVars.end(); ++j )
                    {
                        result += "(" + *j + " = 0 or " + *j + " = 1) and ";
                    }
                }
                else
                {
                    result += "( ";
                }
                std::list<Formula*>::const_iterator it = mpSubformulas->begin();
                // do not quantify variables again.
                result += (*it)->toRedlogFormat( false );
                for( ++it; it != mpSubformulas->end(); ++it )
                {
                    // do not quantify variables again.
                    result += " " + oper + " " + (*it)->toRedlogFormat( false );
                }
                if( withVariables )
                    result += " ) )";
                result += " )";
            }
        }
        return result;
    }

    /**
     * Generates a string displaying the formula as a QEPCAD formula.
     * @param withVariables if true, variables are quantified, otherwise not
     * @param variableIds maps original variable ids to unique indexed variable ids only consisting of letters and numbers
     * @return
     */
    string Formula::toQepcadFormat( bool withVariables, const unordered_map<string, string>& variableIds ) const
    {
        string result = "";
        string oper = Formula::FormulaTypeToString( mType );
        if( mType == AND )
            oper = "/\\";
        if( mType == OR )
            oper = "\\/";
        switch( mType )
        {
            // unary cases
            case TTRUE:
            {
                result += " " + oper + " ";
                break;
            }
            case FFALSE:
            {
                result += " " + oper + " ";
                break;
            }
            case NOT:
            {
                result += " ~[ " + (*mpSubformulas->begin())->toQepcadFormat( withVariables, variableIds ) + " ]";
                break;
            }
            case REALCONSTRAINT:
            {
                string constraintStr = "";
                // replace all variable ids
                GiNaC::exmap symbolMapping;
                for( unordered_map<string, string>::const_iterator vId = variableIds.begin(); vId != variableIds.end(); ++vId )
                {
                    auto realVar = mpConstraintPool->realVariables().find( vId->first );
                    assert( realVar != mpConstraintPool->realVariables().end() );
                    symbolMapping[ realVar->second ] = GiNaC::symbol( vId->second );
                }
                GiNaC::ex lhsAfterReplacing = constraint().lhs().subs( symbolMapping );
                ostringstream sstream;
                sstream << lhsAfterReplacing;
                constraintStr += sstream.str(); 
                // replace all *
                size_t pos = constraintStr.find( "*" );
                while( pos != constraintStr.npos )
                {
                    constraintStr.replace( pos, 1, " " ); // @TODO: dangerous substitution
                    pos = constraintStr.find( "*", pos );
                }
                // print the relation symbol and right-hand side
                // @TODO: adapt relation symbol
                switch( constraint().relation() )
                {
                    case CR_EQ:
                        constraintStr += "  = ";
                        break;
                    case CR_NEQ:
                        constraintStr += " != ";
                        break;
                    case CR_LESS:
                        constraintStr += "  < ";
                        break;
                    case CR_GREATER:
                        constraintStr += "  > ";
                        break;
                    case CR_LEQ:
                        constraintStr += " <= ";
                        break;
                    case CR_GEQ:
                        constraintStr += " >= ";
                        break;
                    default:
                        constraintStr += "  ~ ";
                }
                constraintStr += "0";

                result += constraintStr;
                break;
            }
            case BOOL:
            {
                result += *mpIdentifier + " = 1";
                break;
            }
            default:
            {
                // recursive print of the subformulas
                if( withVariables )
                { // add the variables
                    result += "(";
                    result += variableListToString( ",", variableIds ) + ")\n0\n(E " + variableListToString( ") (E ", variableIds ) + ") [";
                    // Make pseudo Booleans.
                    for( std::set< std::string, strCmp >::const_iterator j = mBooleanVars.begin(); j != mBooleanVars.end(); ++j )
                    {
                        result += "[" + *j + " = 0 \\/ " + *j + " = 1] /\\ ";
                    }
                }
                else
                    result += "[";
                std::list<Formula*>::const_iterator it = mpSubformulas->begin();
                // do not quantify variables again.
                result += (*it)->toQepcadFormat( false, variableIds );
                for( ++it; it != mpSubformulas->end(); ++it )
                {
                    // do not quantify variables again.
                    result += " " + oper + " " + (*it)->toQepcadFormat( false, variableIds );
                }
                if( withVariables )
                    result += " ].";
                else
                    result += "]";
            }
        }
        return result;
    }
}    // namespace smtrat

