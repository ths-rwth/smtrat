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
    {
//        assert( _constraint->relation() != CR_NEQ );
    }

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
//        assert( _formula->getType() != REALCONSTRAINT || _formula->constraint().relation() != CR_NEQ );
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
                _out << _init;
                mpConstraint->printInPrefix( _out );
//                _out << " (" << mActivity << ")";
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

    ostream& operator <<( ostream& _ostream, const Formula& _formula )
    {
        _formula.print( _ostream, "", true );
        return _ostream;
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
                result += mpConstraint->smtlibString();
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

    /**
     *
     * @param _formula
     * @param _keepConstraints
     */
    void Formula::toCNF( Formula& _formula, bool _keepConstraints )
    {
        if( _keepConstraints && (_formula.getPropositions() | ~PROP_IS_IN_CNF) == ~PROP_TRUE ) return;
        Formula* copy = new Formula( _formula.getType() );
        while( !_formula.empty() )
        {
            copy->addSubformula( _formula.pruneBack() );
        }
        _formula.copyAndDelete( new Formula( AND ) );
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
                    _formula.addSubformula( currentFormula );
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
                    if( Formula::resolveNegation( *currentFormula, _keepConstraints ) )
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
                                currentFormula->addSubformula( currentSubformula );
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
                                delete currentFormula;
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
                                if( Formula::resolveNegation( *currentSubformula, _keepConstraints ) )
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
                                Formula* hi = new Formula( Formula::getAuxiliaryBoolean() );
                                while( !currentSubformula->empty() )
                                {
                                    Formula* formulaToAssert = new Formula( OR );
                                    formulaToAssert->addSubformula( new Formula( NOT ) );
                                    formulaToAssert->back()->addSubformula( new Formula( *hi ) );
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
                                assert( currentSubformula->back()->size() == 2 );
                                Formula* rhs = currentSubformula->pruneBack();
                                Formula* lhs = currentSubformula->pruneBack();
                                delete currentSubformula;
                                phis.push_back( new Formula( NOT ) );
                                phis.back()->addSubformula( lhs );
                                phis.push_back( rhs );
                                break;
                            }
                            // (iff lhs_i rhs_i) -> h_i1 h_i2, where (or (not h_i1) lhs_i) (or (not h_i1) rhs_i)
                            //                                       (or (not h_i2) (not lhs_i)) (or (not h_i2) (not rhs_i))  is added to the queue
                            case IFF:
                            {
                                assert( currentSubformula->back()->size() == 2 );
                                Formula* h_i1  = new Formula( Formula::getAuxiliaryBoolean() );
                                Formula* h_i2  = new Formula( Formula::getAuxiliaryBoolean() );
                                Formula* rhs_i = currentSubformula->pruneBack();
                                Formula* lhs_i = currentSubformula->pruneBack();
                                delete currentSubformula;

                                phis.push_back( new Formula( OR ) );
                                phis.back()->addSubformula( new Formula( NOT ) );
                                phis.back()->back()->addSubformula( new Formula( *h_i1 ) );
                                phis.back()->addSubformula( lhs_i );
                                phis.push_back( new Formula( OR ) );
                                phis.back()->addSubformula( new Formula( NOT ) );
                                phis.back()->back()->addSubformula( new Formula( *h_i1 ) );
                                phis.back()->addSubformula( rhs_i );
                                phis.push_back( new Formula( OR ) );
                                phis.back()->addSubformula( new Formula( NOT ) );
                                phis.back()->back()->addSubformula( new Formula( *h_i2 ) );
                                phis.back()->addSubformula( new Formula( NOT ) );
                                phis.back()->back()->addSubformula( new Formula( *lhs_i ) );
                                phis.push_back( new Formula( OR ) );
                                phis.back()->addSubformula( new Formula( NOT ) );
                                phis.back()->back()->addSubformula( new Formula( *h_i2 ) );
                                phis.back()->addSubformula( new Formula( NOT ) );
                                phis.back()->back()->addSubformula( new Formula( *rhs_i ) );

                                currentFormula->addSubformula( h_i1 );
                                currentFormula->addSubformula( h_i2 );
                                break;
                            }
                            // (xor lhs_i rhs_i) -> h_i1 h_i2, where (or (not h_i1) (not lhs_i)) (or (not h_i1) rhs_i)
                            //                                       (or (not h_i2) lhs_i) (or (not h_i2) (not rhs_i))  is added to the queue
                            case XOR:
                            {
                                assert( currentSubformula->back()->size() == 2 );
                                Formula* h_i1  = new Formula( Formula::getAuxiliaryBoolean() );
                                Formula* h_i2  = new Formula( Formula::getAuxiliaryBoolean() );
                                Formula* rhs_i = currentSubformula->pruneBack();
                                Formula* lhs_i = currentSubformula->pruneBack();
                                delete currentSubformula;

                                phis.push_back( new Formula( OR ) );
                                phis.back()->addSubformula( new Formula( NOT ) );
                                phis.back()->back()->addSubformula( new Formula( *h_i1 ) );
                                phis.back()->addSubformula( new Formula( NOT ) );
                                phis.back()->back()->addSubformula( lhs_i );
                                phis.push_back( new Formula( OR ) );
                                phis.back()->addSubformula( new Formula( NOT ) );
                                phis.back()->back()->addSubformula( new Formula( *h_i1 ) );
                                phis.back()->addSubformula( rhs_i );
                                phis.push_back( new Formula( OR ) );
                                phis.back()->addSubformula( new Formula( NOT ) );
                                phis.back()->back()->addSubformula( new Formula( *h_i2 ) );
                                phis.back()->addSubformula( new Formula( *lhs_i ) );
                                phis.push_back( new Formula( OR ) );
                                phis.back()->addSubformula( new Formula( NOT ) );
                                phis.back()->back()->addSubformula( new Formula( *h_i2 ) );
                                phis.back()->addSubformula( new Formula( NOT ) );
                                phis.back()->back()->addSubformula( new Formula( *rhs_i ) );

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
                    if( !currentFormula->empty() ) _formula.addSubformula( currentFormula );
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
                    delete currentFormula;
                    currentFormula = new Formula( OR );
                    currentFormula->addSubformula( new Formula( NOT ) );
                    currentFormula->back()->addSubformula( lhs );
                    currentFormula->addSubformula( rhs );
                    subformulasToTransform.push_back( currentFormula );
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
                    Formula* h1     = new Formula( Formula::getAuxiliaryBoolean() );
                    Formula* h2     = new Formula( Formula::getAuxiliaryBoolean() );
                    Formula* clause = new Formula( OR );
                    clause->addSubformula( h1 );
                    clause->addSubformula( h2 );
                    _formula.addSubformula( clause );
                    // Append (or (not h1) lhs), (or (not h1) rhs), (or (not h2) (not lhs)) and (or (not h2) (not rhs)) to _formulasToAssert.
                    Formula* formulaToAssertA = new Formula( OR );
                    formulaToAssertA->addSubformula( new Formula( NOT ) );
                    formulaToAssertA->back()->addSubformula( new Formula( *h1 ) );
                    formulaToAssertA->addSubformula( lhs );    // Once it can be used, otherwise copy it,
                    subformulasToTransform.push_back( formulaToAssertA );
                    Formula* formulaToAssertB = new Formula( OR );
                    formulaToAssertB->addSubformula( new Formula( NOT ) );
                    formulaToAssertB->back()->addSubformula( new Formula( *h1 ) );
                    formulaToAssertB->addSubformula( rhs );    // Once it can be used, otherwise copy it,
                    subformulasToTransform.push_back( formulaToAssertB );
                    Formula* formulaToAssertC = new Formula( OR );
                    formulaToAssertC->addSubformula( new Formula( NOT ) );
                    formulaToAssertC->back()->addSubformula( new Formula( *h2 ) );
                    formulaToAssertC->addSubformula( new Formula( NOT ) );
                    formulaToAssertC->back()->addSubformula( new Formula( *lhs ) );
                    subformulasToTransform.push_back( formulaToAssertC );
                    Formula* formulaToAssertD = new Formula( OR );
                    formulaToAssertD->addSubformula( new Formula( NOT ) );
                    formulaToAssertD->back()->addSubformula( new Formula( *h2 ) );
                    formulaToAssertD->addSubformula( new Formula( NOT ) );
                    formulaToAssertD->back()->addSubformula( new Formula( *rhs ) );
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
                    Formula* h1     = new Formula( Formula::getAuxiliaryBoolean() );
                    Formula* h2     = new Formula( Formula::getAuxiliaryBoolean() );
                    Formula* clause = new Formula( OR );
                    clause->addSubformula( h1 );
                    clause->addSubformula( h2 );
                    _formula.addSubformula( clause );
                    // Append (or (not h1) (not lhs)), (or (not h1) rhs), (or (not h2) lhs) and (or (not h2) (not rhs)) to _formulasToAssert.
                    Formula* formulaToAssertA = new Formula( OR );
                    formulaToAssertA->addSubformula( new Formula( NOT ) );
                    formulaToAssertA->back()->addSubformula( new Formula( *h1 ) );
                    formulaToAssertA->addSubformula( new Formula( NOT ) );
                    formulaToAssertA->back()->addSubformula( lhs );    // Once it can be used, otherwise copy it,
                    subformulasToTransform.push_back( formulaToAssertA );
                    Formula* formulaToAssertB = new Formula( OR );
                    formulaToAssertB->addSubformula( new Formula( NOT ) );
                    formulaToAssertB->back()->addSubformula( new Formula( *h1 ) );
                    formulaToAssertB->addSubformula( rhs );    // Once it can be used, otherwise copy it,
                    subformulasToTransform.push_back( formulaToAssertB );
                    Formula* formulaToAssertC = new Formula( OR );
                    formulaToAssertC->addSubformula( new Formula( NOT ) );
                    formulaToAssertC->back()->addSubformula( new Formula( *h2 ) );
                    formulaToAssertC->addSubformula( new Formula( *lhs ) );
                    subformulasToTransform.push_back( formulaToAssertC );
                    Formula* formulaToAssertD = new Formula( OR );
                    formulaToAssertD->addSubformula( new Formula( NOT ) );
                    formulaToAssertD->back()->addSubformula( new Formula( *h2 ) );
                    formulaToAssertD->addSubformula( new Formula( NOT ) );
                    formulaToAssertD->back()->addSubformula( new Formula( *rhs ) );
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
            _formula.copyAndDelete( new Formula( TTRUE ) );
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
                if( _keepConstraint ) return false;
                else
                {
                    const Constraint* constraint = subformula->pConstraint();
                    _formula.pop_back();
                    switch( constraint->relation() )
                    {
                        case CR_EQ:
                        {
                            _formula.copyAndDelete( new Formula( OR ) );
                            _formula.addSubformula( new Formula( Formula::newConstraint( constraint->lhs(), CR_LESS ) ) );
                            _formula.addSubformula( new Formula( Formula::newConstraint( -constraint->lhs(), CR_LESS ) ) );
                            return true;
                        }
                        case CR_LEQ:
                        {
                            _formula.copyAndDelete( new Formula( Formula::newConstraint( -constraint->lhs(), CR_LESS ) ) );
                            return false;
                        }
                        case CR_LESS:
                        {
                            _formula.copyAndDelete( new Formula( Formula::newConstraint( -constraint->lhs(), CR_LEQ ) ) );
                            return false;
                        }
                        case CR_NEQ:
                        {
                            _formula.copyAndDelete( new Formula( Formula::newConstraint( constraint->lhs(), CR_EQ ) ) );
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
                _formula.copyAndDelete( _formula.pruneBack() );
                return true;
            }
            case FFALSE:
            {
                /*
                    * (not false)  ->  true
                    */
                _formula.copyAndDelete( _formula.pruneBack() );
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
                _formula.copyAndDelete( new Formula( OR ) );
                while( !subsubformulas.empty() )
                {
                    _formula.addSubformula( new Formula( NOT ) );
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
                _formula.copyAndDelete( new Formula( AND ) );
                while( !subsubformulas.empty() )
                {
                    _formula.addSubformula( new Formula( NOT ) );
                    _formula.back()->addSubformula( subsubformulas.back() );
                    subsubformulas.pop_back();
                }
                return true;
            }
            case IMPLIES:
            {
                assert( subformula->size() == 2 );

                /*
                    * (not (implies lhs rhs))  ->  (and rhs (not lhs))
                    */
                Formula* rhsOfSubformula = subformula->pruneBack();
                Formula* lhsOfSubformula = subformula->pruneBack();
                _formula.pop_back();
                _formula.copyAndDelete( new Formula( AND ) );
                _formula.addSubformula( lhsOfSubformula );
                _formula.addSubformula( new Formula( NOT ) );
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
                _formula.copyAndDelete( new Formula( XOR ) );
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
                _formula.copyAndDelete( new Formula( IFF ) );
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
}    // namespace smtrat

