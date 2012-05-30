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
    Formula::Formula()
    {
        mType                 = TTRUE;
        mRealValuedVars       = GiNaC::symtab();
        mPropositions         = Condition();
        mPropositionsUptodate = false;
        mpFather              = NULL;
        updateID();
    }

    Formula::Formula( const Type _type )
    {
        mType = _type;
        if( _type != TTRUE && _type != FFALSE )
        {
            mpSubformulas = new vector<Formula*>();
        }
        else if( _type == TTRUE )
        {
            mType = TTRUE;
        }
        else
        {
            mType = FFALSE;
        }
        mPropositions         = Condition();
        mPropositionsUptodate = false;
        mpFather              = NULL;
        assert( _type != REALCONSTRAINT && _type != BOOL );
        mRealValuedVars = GiNaC::symtab();
        updateID();
    }

    Formula::Formula( const string& _id )
    {
        mType                 = BOOL;
        mpIdentifier          = new string( _id );
        mpFather              = NULL;
        mRealValuedVars       = GiNaC::symtab();
        mPropositions         = Condition();
        mPropositionsUptodate = false;
        updateID();
    }

    Formula::Formula( const Constraint* _constraint )
    {
        mType           = REALCONSTRAINT;
        mpFather        = NULL;
        mpConstraint    = _constraint;
        mRealValuedVars = GiNaC::symtab();
        mRealValuedVars.insert( _constraint->variables().begin(), _constraint->variables().end() );
        mPropositions         = Condition();
        mPropositionsUptodate = false;
        updateID();
    }

    Formula::Formula( const Constraint& _constraint )
    {
        mType        = REALCONSTRAINT;
        mpFather     = NULL;
        mpConstraint = new Constraint( _constraint );
        mRealValuedVars.insert( _constraint.variables().begin(), _constraint.variables().end() );
        mPropositions         = Condition();
        mPropositionsUptodate = false;
        updateID();
    }

    Formula::Formula( const Formula& _formula )
    {
        mType    = _formula.getType();
        mpFather = NULL;
        if( _formula.getType() == REALCONSTRAINT )
        {
            mpConstraint = new Constraint( _formula.constraint() );
        }
        else if( _formula.getType() != BOOL && _formula.getType() != TTRUE && _formula.getType() != FFALSE )
        {
            mpSubformulas = new vector<Formula*>();
            for( const_iterator subFormula = _formula.subformulas().begin(); subFormula != _formula.subformulas().end(); ++subFormula )
            {
                addSubformula( new Formula( **subFormula ) );
            }
        }
        else if( _formula.getType() == BOOL )
        {
            mpIdentifier = new string( _formula.identifier() );
        }
        mRealValuedVars       = GiNaC::symtab( _formula.realValuedVars() );
        mPropositions         = Condition();
        mPropositionsUptodate = false;
        updateID();
    }

    Formula::~Formula()
    {
        if( mType == REALCONSTRAINT )
        {
            delete mpConstraint;
        }
        else if( mType != BOOL )
        {
            while( !mpSubformulas->empty() )
            {
                Formula* pSubForm = mpSubformulas->back();
                mpSubformulas->pop_back();
                delete pSubForm;
            }
            delete mpSubformulas;
        }
        else if( mType == BOOL )
        {
            delete mpIdentifier;
        }
    }

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
                    for( vector<Formula*>::iterator subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
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
                    for( vector<Formula*>::iterator subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
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
                    for( vector<Formula*>::iterator subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
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
                    for( vector<Formula*>::iterator subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
                    {
                        mPropositions |= ((*subFormula)->getPropositions() & WEAK_CONDITIONS);
                    }
                    break;
                }
                case IFF:
                {
                    mPropositions |= PROP_IS_IN_NNF | PROP_VARIABLE_DEGREE_LESS_THAN_THREE;
                    for( vector<Formula*>::iterator subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
                    {
                        mPropositions |= ((*subFormula)->getPropositions() & WEAK_CONDITIONS);
                    }
                    break;
                }
                case XOR:
                {
                    mPropositions |= PROP_IS_IN_NNF | PROP_VARIABLE_DEGREE_LESS_THAN_THREE;
                    for( vector<Formula*>::iterator subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
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

    unsigned Formula::getMaxID() const
    {
        if( mType == BOOL || mType == REALCONSTRAINT || mType == TTRUE || mType == FFALSE )
        {
            return mId;
        }
        else
        {
            if( mpSubformulas->empty() )
            {
                return mId;
            }
            else
            {
                return mpSubformulas->back()->getMaxID();
            }
        }
    }

    void Formula::setFather( Formula* _father )
    {
        assert( mpFather == NULL );
        mpFather = _father;
    }

    void Formula::updateID()
    {
        if( mpFather != NULL )
        {
            mId = mpFather->getMaxID() + 1;
        }
        else
        {
            mId = 1;
        }
    }

    void Formula::addSubformula( Formula* _formula )
    {
        assert( mType != REALCONSTRAINT && mType != BOOL && mType != TTRUE && mType != FFALSE );
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
        _formula->updateID();

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

    void Formula::addSubformula( const Constraint* _constraint )
    {
        assert( mType != REALCONSTRAINT && mType != BOOL && mType != TTRUE && mType != FFALSE );

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

    void Formula::pop_back()
    {
        assert( mType != BOOL && mType != REALCONSTRAINT && mType != TTRUE && mType != FFALSE );
        Formula* pSubForm = mpSubformulas->back();
        mpSubformulas->pop_back();
        delete pSubForm;
        mPropositionsUptodate = false;
    }

    void Formula::erase( unsigned _position )
    {
        assert( mType != BOOL && mType != REALCONSTRAINT && mType != TTRUE && mType != FFALSE );
        assert( _position < mpSubformulas->size() );
        std::vector<Formula*>::iterator subFormula = mpSubformulas->begin();
        unsigned                        pos        = 0;
        while( subFormula != mpSubformulas->end() )
        {
            if( pos == _position )
            {
                Formula* pSubFormula = *subFormula;
                mpSubformulas->erase( subFormula );
                delete pSubFormula;
                mPropositionsUptodate = false;
                break;
            }
            ++subFormula;
            ++pos;
        }
    }

    void Formula::erase( const Formula* _formula )
    {
        assert( mType != BOOL && mType != REALCONSTRAINT && mType != TTRUE && mType != FFALSE );
        std::vector<Formula*>::iterator subFormula = mpSubformulas->begin();
        while( subFormula != mpSubformulas->end() )
        {
            if( *subFormula == _formula )
            {
                Formula* pSubFormula = *subFormula;
                mpSubformulas->erase( subFormula );
                delete pSubFormula;
                mPropositionsUptodate = false;
                break;
            }
            ++subFormula;
        }
        assert( false );
    }

    Formula* Formula::pruneBack()
    {
        assert( mType != BOOL && mType != REALCONSTRAINT && mType != TTRUE && mType != FFALSE );
        assert( !mpSubformulas->empty() );
        Formula* result = mpSubformulas->back();
        result->resetFather();
        mpSubformulas->pop_back();
        mPropositionsUptodate = false;
        return result;
    }

    void Formula::clear()
    {
        assert( mType != BOOL && mType != REALCONSTRAINT && mType != TTRUE && mType != FFALSE );
        while( !mpSubformulas->empty() )
        {
            Formula* pSubForm = mpSubformulas->back();
            mpSubformulas->pop_back();
            delete pSubForm;
        }
        mPropositionsUptodate = false;
    }

    void Formula::notSolvableBy( ModuleType _moduleType )
    {
        switch( _moduleType )
        {
            case MT_SimplifierModule:
            {
                mPropositions |= PROP_CANNOT_BE_SOLVED_BY_SIMPLIFIERMODULE;
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
            default:
            {
            }
        }
    }

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
                _out << _init << mpConstraint->toString();
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
            std::vector<Formula*>::const_iterator subFormula = mpSubformulas->begin();
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

            /*
                        printPropositions( _out, _init );
            */
        }
    }

    void Formula::printPropositions( ostream& _out, const string _init ) const
    {
        _out << _init << " Propositions are up to date?  " << (mPropositionsUptodate ? "Yes." : "No.") << endl;
        _out << _init << " PROP_IS_IN_NNF                               = ";
        _out << ((~PROP_IS_IN_NNF | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_IS_IN_CNF                               = ";
        _out << ((~PROP_IS_IN_CNF | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_IS_PURE_CONJUNCTION                     = ";
        _out << ((~PROP_IS_PURE_CONJUNCTION | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_IS_A_CLAUSE                             = ";
        _out << ((~PROP_IS_A_CLAUSE | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_IS_A_LITERAL                            = ";
        _out << ((~PROP_IS_A_LITERAL | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_IS_AN_ATOM                              = ";
        _out << ((~PROP_IS_AN_ATOM | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_VARIABLE_DEGREE_LESS_THAN_FIVE          = ";
        _out << ((~PROP_VARIABLE_DEGREE_LESS_THAN_FIVE | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_VARIABLE_DEGREE_LESS_THAN_FOUR          = ";
        _out << ((~PROP_VARIABLE_DEGREE_LESS_THAN_FOUR | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_VARIABLE_DEGREE_LESS_THAN_THREE         = ";
        _out << ((~PROP_VARIABLE_DEGREE_LESS_THAN_THREE | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " STRONG_CONDITIONS                            = ";
        _out << ((~STRONG_CONDITIONS | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_CONTAINS_EQUATION                       = ";
        _out << ((~PROP_CONTAINS_EQUATION | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_CONTAINS_INEQUALITY                     = ";
        _out << ((~PROP_CONTAINS_INEQUALITY | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_CONTAINS_STRICT_INEQUALITY              = ";
        _out << ((~PROP_CONTAINS_STRICT_INEQUALITY | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_CONTAINS_LINEAR_POLYNOMIAL              = ";
        _out << ((~PROP_CONTAINS_LINEAR_POLYNOMIAL | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_CONTAINS_NONLINEAR_POLYNOMIAL           = ";
        _out << ((~PROP_CONTAINS_NONLINEAR_POLYNOMIAL | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_CONTAINS_MULTIVARIATE_POLYNOMIAL        = ";
        _out << ((~PROP_CONTAINS_MULTIVARIATE_POLYNOMIAL | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " WEAK_CONDITIONS                              = ";
        _out << ((~WEAK_CONDITIONS | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_CANNOT_BE_SOLVED_BY_SIMPLIFIERMODULE    = ";
        _out << ((~PROP_CANNOT_BE_SOLVED_BY_SIMPLIFIERMODULE | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_CANNOT_BE_SOLVED_BY_GROEBNERMODULE      = ";
        _out << ((~PROP_CANNOT_BE_SOLVED_BY_GROEBNERMODULE | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_CANNOT_BE_SOLVED_BY_VSMODULE            = ";
        _out << ((~PROP_CANNOT_BE_SOLVED_BY_VSMODULE | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_CANNOT_BE_SOLVED_BY_UNIVARIATECADMODULE = ";
        _out << ((~PROP_CANNOT_BE_SOLVED_BY_UNIVARIATECADMODULE | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_CANNOT_BE_SOLVED_BY_CADMODULE           = ";
        _out << ((~PROP_CANNOT_BE_SOLVED_BY_CADMODULE | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_CANNOT_BE_SOLVED_BY_SATMODULE           = ";
        _out << ((~PROP_CANNOT_BE_SOLVED_BY_SATMODULE | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_CANNOT_BE_SOLVED_BY_LRAMODULE           = ";
        _out << ((~PROP_CANNOT_BE_SOLVED_BY_LRAMODULE | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_CANNOT_BE_SOLVED_BY_PREPROMODULE        = ";
        _out << ((~PROP_CANNOT_BE_SOLVED_BY_PREPROMODULE | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
        _out << _init << " PROP_CANNOT_BE_SOLVED_BY_CNFERMODULE         = ";
        _out << ((~PROP_CANNOT_BE_SOLVED_BY_CNFERMODULE | mPropositions) == ~PROP_TRUE ? "1" : "0") << endl;
    }

    void Formula::FormulaToConstraints( vector<const Constraint*>& _const ) const
    {
        if( mType == REALCONSTRAINT )
        {
            _const.push_back( mpConstraint );
        }
        else if( mpSubformulas->size() != 0 )
        {
            for( const_iterator subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
            {
                (*subFormula)->FormulaToConstraints( _const );
            }
        }
    }
}    // namespace smtrat

