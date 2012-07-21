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
 * @since 2012-02-09
 * @version 2012-02-09
 */

#include "Formula.h"

using namespace std;

namespace smtrat
{
    ConstraintPool Formula::mConstraintPool             = ConstraintPool( 10000 );
    const string   Formula::mAuxiliaryBooleanNamePrefix = string( "h_b_" );
    unsigned       Formula::mAuxiliaryBooleanCounter    = 0;
    const string   Formula::mAuxiliaryRealNamePrefix    = string( "h_r_" );
    unsigned       Formula::mAuxiliaryRealCounter       = 0;

    Formula::Formula():
        mActivity( 0 ),
        mType( TTRUE ),
        mRealValuedVars(),
        mpSubformulas( NULL ),
        mpFather( NULL ),
        mPropositions(),
        mPropositionsUptodate( false )
    {}

    Formula::Formula( const Type _type ):
        mActivity( 0 ),
        mType( _type ),
        mRealValuedVars(),
        mpSubformulas( (_type != TTRUE && _type != FFALSE) ? new list<Formula*>() : NULL ),
        mpFather( NULL ),
        mPropositions(),
        mPropositionsUptodate( false )
    {
        assert( _type != REALCONSTRAINT && _type != BOOL );
    }

    Formula::Formula( const string& _id ):
        mActivity( 0 ),
        mType( BOOL ),
        mRealValuedVars(),
        mpIdentifier( new string( _id ) ),
        mpFather( NULL ),
        mPropositions(),
        mPropositionsUptodate( false )
    {}

    Formula::Formula( const Constraint* _constraint ):
        mActivity( 0 ),
        mType( REALCONSTRAINT ),
        mRealValuedVars( _constraint->variables() ),
        mpConstraint( _constraint ),
        mpFather( NULL ),
        mPropositions(),
        mPropositionsUptodate( false )
    {}

    Formula::Formula( const Formula& _formula ):
        mActivity( 0 ),
        mType( _formula.getType() ),
        mRealValuedVars( _formula.realValuedVars() ),
        mpFather( NULL ),
        mPropositions(),
        mPropositionsUptodate( false )
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
                addSubformula( new Formula( **subFormula ) );
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
                    mPropositions |= STRONG_CONDITIONS;
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
                    mPropositions |= PROP_IS_A_LITERAL | PROP_VARIABLE_DEGREE_LESS_THAN_THREE;
                    for( list<Formula*>::iterator subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
                    {
                        if( ((*subFormula)->getPropositions() | ~PROP_IS_AN_ATOM) != ~PROP_TRUE )
                        {
                            mPropositions &= ~PROP_IS_IN_NNF;
                        }
                        mPropositions |= ((*subFormula)->getPropositions() & WEAK_CONDITIONS);
                    }
                    break;
                }
                case OR:
                {
                    mPropositions |= PROP_IS_A_CLAUSE | PROP_VARIABLE_DEGREE_LESS_THAN_THREE;
                    for( list<Formula*>::iterator subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
                    {
                        if( ((*subFormula)->getPropositions() | ~PROP_IS_A_LITERAL) != ~PROP_TRUE )
                        {
                            mPropositions &= ~PROP_IS_A_CLAUSE;
                        }
                        mPropositions |= ((*subFormula)->getPropositions() & WEAK_CONDITIONS);
                    }
                    break;
                }
                case AND:
                {
                    mPropositions |= PROP_IS_PURE_CONJUNCTION | PROP_VARIABLE_DEGREE_LESS_THAN_THREE;
                    for( list<Formula*>::iterator subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
                    {
                        if( ((*subFormula)->getPropositions() | ~PROP_IS_A_CLAUSE) != ~PROP_TRUE )
                        {
                            mPropositions &= ~PROP_IS_IN_CNF;
                        }
                        else if( ((*subFormula)->getPropositions() | ~PROP_IS_A_LITERAL) != ~PROP_TRUE )
                        {
                            mPropositions &= ~PROP_IS_PURE_CONJUNCTION;
                            mPropositions |= PROP_IS_IN_CNF;
                        }
                        mPropositions |= ((*subFormula)->getPropositions() & WEAK_CONDITIONS);
                    }
                    break;
                }
                case IMPLIES:
                {
                    mPropositions |= PROP_IS_IN_NNF | PROP_VARIABLE_DEGREE_LESS_THAN_THREE;
                    for( list<Formula*>::iterator subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
                    {
                        mPropositions |= ((*subFormula)->getPropositions() & WEAK_CONDITIONS);
                    }
                    break;
                }
                case IFF:
                {
                    mPropositions |= PROP_IS_IN_NNF | PROP_VARIABLE_DEGREE_LESS_THAN_THREE;
                    for( list<Formula*>::iterator subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
                    {
                        mPropositions |= ((*subFormula)->getPropositions() & WEAK_CONDITIONS);
                    }
                    break;
                }
                case XOR:
                {
                    mPropositions |= PROP_IS_IN_NNF | PROP_VARIABLE_DEGREE_LESS_THAN_THREE;
                    for( list<Formula*>::iterator subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
                    {
                        mPropositions |= ((*subFormula)->getPropositions() & WEAK_CONDITIONS);
                    }
                    break;
                }
                default:
                {
                    cerr << "Undefined operator!" << endl;
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

        /*
         * Add the formula.
         */
        mpSubformulas->push_back( _formula );

        //Adapt the conditions, if they are up to date. (In this case very cheap)
        if( mPropositionsUptodate )
        {
            if( mType == AND )
            {
                if( (_formula->getPropositions() | ~PROP_IS_A_LITERAL) != ~PROP_TRUE )
                {
                    mPropositions &= ~PROP_IS_PURE_CONJUNCTION;
                }
                else if( (_formula->getPropositions() | ~PROP_IS_A_CLAUSE) != ~PROP_TRUE )
                {
                    mPropositions &= ~PROP_IS_IN_CNF;
                }
            }
            else if( mType == OR )
            {
                if( (_formula->getPropositions() | ~PROP_IS_A_LITERAL) != ~PROP_TRUE )
                {
                    mPropositions &= ~PROP_IS_A_CLAUSE;
                }
            }
            else if( mType == NOT )
            {
                if( (_formula->getPropositions() | ~PROP_IS_AN_ATOM) != ~PROP_TRUE )
                {
                    mPropositions &= ~PROP_IS_IN_NNF;
                }
            }
            mPropositions &= (_formula->getPropositions() | ~STRONG_CONDITIONS);
            mPropositions |= (_formula->getPropositions() & WEAK_CONDITIONS);
            mPropositions &= ~SOLVABLE_CONDITIONS;
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
            mPropositions &= ~SOLVABLE_CONDITIONS;
        }
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
     * @param _position
     */
    void Formula::erase( unsigned _position )
    {
        assert( isBooleanCombination() );
        assert( _position < mpSubformulas->size() );
        iterator subFormula = mpSubformulas->begin();
        unsigned pos = 0;
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
        iterator subFormula = mpSubformulas->begin();
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
        iterator result = mpSubformulas->erase( _subformula );
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
     * @param _position
     * @return
     */
    Formula* Formula::prune( unsigned _position )
    {
        assert( isBooleanCombination() );
        assert( _position < mpSubformulas->size() );
        iterator subFormula = mpSubformulas->begin();
        unsigned pos = 0;
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
     * @param _moduleType
     */
    void Formula::notSolvableBy( ModuleType _moduleType )
    {
        switch( _moduleType )
        {
            case MT_SmartSimplifier:
            {
                mPropositions |= PROP_CANNOT_BE_SOLVED_BY_SMARTSIMPLIFIER;
                break;
            }
            case MT_GroebnerModule:
            {
                mPropositions |= PROP_CANNOT_BE_SOLVED_BY_GROEBNERMODULE;
                break;
            }
            case MT_VSModule:
            {
                mPropositions |= PROP_CANNOT_BE_SOLVED_BY_VSMODULE;
                break;
            }
            case MT_UnivariateCADModule:
            {
                mPropositions |= PROP_CANNOT_BE_SOLVED_BY_UNIVARIATECADMODULE;
                break;
            }
            case MT_CADModule:
            {
                mPropositions |= PROP_CANNOT_BE_SOLVED_BY_CADMODULE;
                break;
            }
            case MT_SATModule:
            {
                mPropositions |= PROP_CANNOT_BE_SOLVED_BY_SATMODULE;
                break;
            }
            case MT_LRAModule:
            {
                mPropositions |= PROP_CANNOT_BE_SOLVED_BY_LRAMODULE;
                break;
            }
            case MT_LRAOneModule:
            {
                mPropositions |= PROP_CANNOT_BE_SOLVED_BY_LRAONEMODULE;
                break;
            }
            case MT_LRATwoModule:
            {
                mPropositions |= PROP_CANNOT_BE_SOLVED_BY_LRATWOMODULE;
                break;
            }
            case MT_PreProModule:
            {
                mPropositions |= PROP_CANNOT_BE_SOLVED_BY_PREPROMODULE;
                break;
            }
            case MT_PreProCNFModule:
            {
                mPropositions |= PROP_CANNOT_BE_SOLVED_BY_PREPROCNFMODULE;
                break;
            }
            case MT_CNFerModule:
            {
                mPropositions |= PROP_CANNOT_BE_SOLVED_BY_CNFERMODULE;
                break;
            }
            case MT_SingleVSModule:
            {
                mPropositions |= PROP_CANNOT_BE_SOLVED_BY_SINGLEVSMODULE;
                break;
            }
            case MT_FourierMotzkinSimplifier:
            {
                mPropositions |= PROP_CANNOT_BE_SOLVED_BY_FOURIERMOTZKINSIMPLIFIER;
                break;
            }
            default:
            {
            }
        }
    }

    /**
     *
     * @param _constraint
     */
    void Formula::addConstraintPropositions( const Constraint& _constraint )
    {
        switch( _constraint.highestDegree() )
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
    }

    /**
     *
     * @param _out
     * @param _init
     * @param _onOneLine
     */
    void Formula::print( ostream& _out, const string _init, bool _onOneLine ) const
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
                oper = "iff";
                break;
            }
            case XOR:
            {
                oper = "xor";
                break;
            }
            case IMPLIES:
            {
                oper = "implies";
                break;
            }
            case BOOL:
            {
                _out << _init << *mpIdentifier;
                break;
            }
            case REALCONSTRAINT:
            {
                _out << _init << *mpConstraint << " (" << mActivity << ")";
                break;
            }
            case TTRUE:
            {
                _out << _init << "True";
                break;
            }
            case FFALSE:
            {
                _out << _init << "False";
                break;
            }
            default:
            {
                _out << _init << "Undefined";
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
                    (*subFormula)->print( _out, "", _onOneLine );
                    _out << " ";
                }
                else
                {
                    (*subFormula)->print( _out, _init + "   ", _onOneLine );
                    _out << endl;
                }
                ++subFormula;
            }
            _out << _init << ")";
        }
        if( mpFather == NULL &&!_onOneLine )
        {
            _out << endl;
        }
    }

    string Formula::toString() const
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
                result += "(iff";
                break;
            }
            case XOR:
            {
                result += "(xor";
                break;
            }
            case IMPLIES:
            {
                result += "(implies";
                break;
            }
            case BOOL:
            {
                result += *mpIdentifier;
                break;
            }
            case REALCONSTRAINT:
            {
                result += mpConstraint->toPrefixString();
                break;
            }
            case TTRUE:
            {
                result += "True";
                break;
            }
            case FFALSE:
            {
                result += "False";
                break;
            }
            default:
            {
                result += "Undefined";
            }
        }
        if( isBooleanCombination() )
        {
            std::list<Formula*>::const_iterator subformula = mpSubformulas->begin();
            while( subformula != mpSubformulas->end() )
            {
                result += " " + (*subformula)->toString();
                ++subformula;
            }
            result += ")";
        }
        return result;
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
}    // namespace smtrat

