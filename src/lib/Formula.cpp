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
 * @author Florian Corzilius
 * @author Ulrich Loup
 * @author Sebastian Junges
 * @since 2012-02-09
 * @version 2013-10-21
 */

//#define REMOVE_LESS_EQUAL_IN_CNF_TRANSFORMATION
//#define REMOVE_UNEQUAL_IN_CNF_TRANSFORMATION

#include "Formula.h"

using namespace std;

namespace smtrat
{
    unique_ptr<ConstraintPool> Formula::mpConstraintPool = unique_ptr<ConstraintPool>(new ConstraintPool());

    Formula::Formula():
        mDeducted( false ),
        mPropositionsUptodate( false ),
        mActivity( 0 ),
        mDifficulty(0),
        mType( TTRUE ),
        mpConstraint( mpConstraintPool->consistentConstraint() ),
        mpFather( NULL ),
        mPropositions()
    {}

    Formula::Formula( const Type _type ):
        mDeducted( false ),
        mPropositionsUptodate( false ),
        mActivity( 0 ),
        mDifficulty( 0 ),
        mType( _type ),
        mpFather( NULL ),
        mPropositions()
    {
        assert( _type != CONSTRAINT && _type != BOOL );
        switch( _type )
        {
            case TTRUE:
                mpConstraint = mpConstraintPool->consistentConstraint();
                break;
            case FFALSE:
                mpConstraint = mpConstraintPool->inconsistentConstraint();
                break;
            default:
                mpSubformulas = new list<Formula*>();
        }
    }

    Formula::Formula( const string* _booleanVarName ):
        mDeducted( false ),
        mPropositionsUptodate( false ),
        mActivity( 0 ),
        mDifficulty( 0 ),
        mType( BOOL ),
        mpIdentifier( _booleanVarName ),
        mpFather( NULL ),
        mPropositions()
    {
        assert( constraintPool().booleanExistsAlready( *_booleanVarName ) );
    }

    Formula::Formula( const Constraint* _constraint ):
        mDeducted( false ),
        mPropositionsUptodate( false ),
        mActivity( 0 ),
        mDifficulty( 0 ),
        mpFather( NULL ),
        mPropositions()
    {
        switch(_constraint->isConsistent())
        {
            case 0: 
                mType = FFALSE;
                mpConstraint = mpConstraintPool->inconsistentConstraint();
                break;
            case 1: 
                mType = TTRUE;
                mpConstraint = mpConstraintPool->consistentConstraint();
                break;
            case 2: 
                mType = CONSTRAINT;
                mpConstraint = _constraint;
                break;
            default:
                assert(false);
        }
    }

    Formula::Formula( const Formula& _formula ):
        mDeducted( false ),
        mPropositionsUptodate( _formula.mPropositionsUptodate ),
        mActivity( _formula.mActivity ),
        mDifficulty( _formula.mDifficulty ),
        mType( _formula.getType() ),
        mpFather( NULL ),
        mPropositions(_formula.mPropositionsUptodate ? _formula.proposition(): Condition())
    {
        assert( &_formula != this );

        if( _formula.getType() == CONSTRAINT )
            mpConstraint = _formula.pConstraint();
        else if( isBooleanCombination() )
        {
            mpSubformulas = new list<Formula*>();
            for( const_iterator subFormula = _formula.subformulas().begin(); subFormula != _formula.subformulas().end(); ++subFormula )
                addSubformula( new Formula( **subFormula ));
        }
        else if( _formula.getType() == BOOL )
            mpIdentifier = _formula.mpIdentifier;
    }

    Formula::~Formula()
    {
        if( mType != BOOL && mType != CONSTRAINT && mType != TTRUE && mType != FFALSE )
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

    void Formula::copyAndDelete( Formula* _formula )
    {
        assert( _formula != this );
        mType = _formula->getType();
        mDifficulty = _formula->difficulty();
        if( _formula->getType() == BOOL )
        {
            if( isBooleanCombination() )
                delete mpSubformulas;
            mpIdentifier = _formula->mpIdentifier;
        }
        else if( _formula->getType() == CONSTRAINT )
        {
            if( isBooleanCombination() )
                delete mpSubformulas;
            mpConstraint = _formula->pConstraint();
        }
        else if( _formula->getType() == TTRUE || _formula->getType() == FFALSE )
        {
            if( isBooleanCombination() )
                delete mpSubformulas;
            mpSubformulas = NULL;
        }
        else
        {
            if( !isBooleanCombination() )
                mpSubformulas = new list<Formula*>();
            while( !_formula->empty() )
                addSubformula( _formula->pruneFront() );
        }
        delete _formula;
    }

    void Formula::addSubformula( Formula* _formula )
    {
        assert( isBooleanCombination() );
        assert( mType != NOT || mpSubformulas->empty() );
        _formula->setFather( this );
        // Add the formula.
        mpSubformulas->push_back( _formula );
        // Adapt the conditions, if they are up to date. (In this case very cheap)
        if( mPropositionsUptodate )
        {
            Condition condOfSubformula = _formula->getPropositions();
            if( mType == AND )
            {
                if( !(PROP_IS_A_LITERAL<=condOfSubformula) )
                    mPropositions &= ~PROP_IS_PURE_CONJUNCTION;
                else if( !(PROP_IS_A_CLAUSE<=condOfSubformula) )
                {
                    mPropositions &= ~PROP_IS_PURE_CONJUNCTION;
                    mPropositions &= ~PROP_IS_IN_CNF;
                }
            }
            else if( mType == OR )
            {
                if( !(PROP_IS_A_LITERAL<=condOfSubformula) )
                    mPropositions &= ~PROP_IS_A_CLAUSE;
            }
            if( !(PROP_IS_IN_NNF<=condOfSubformula) )
                mPropositions &= ~PROP_IS_IN_NNF;
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
                mPropositions &= ~PROP_VARIABLE_DEGREE_LESS_THAN_THREE;
            mPropositions |= (condOfSubformula & WEAK_CONDITIONS);
        }
    }

    Formula::iterator Formula::replace( Formula::iterator _toReplace, Formula* _replacement )
    {
        assert( isBooleanCombination() );
        assert( _toReplace != mpSubformulas->end() );
        Formula* pSubFormula = *_toReplace;
        Formula::iterator result = mpSubformulas->erase( _toReplace );
        delete pSubFormula;
        _replacement->setFather( this );
        result = mpSubformulas->insert( result, _replacement );
        mPropositionsUptodate = false;
        return result;
    }
    
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
                case CONSTRAINT:
                {
                    mPropositions |= STRONG_CONDITIONS;
                    addConstraintPropositions( *mpConstraint );
                    break;
                }
                case NOT:
                {
                    Condition subFormulaConds = (*mpSubformulas->begin())->getPropositions();
                    if( PROP_IS_AN_ATOM <= subFormulaConds )
                        mPropositions |= PROP_IS_A_CLAUSE | PROP_IS_A_LITERAL | PROP_IS_IN_CNF | PROP_IS_PURE_CONJUNCTION;
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
                            mPropositions &= ~PROP_IS_IN_NNF;
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
                            mPropositions &= ~PROP_IS_PURE_CONJUNCTION;
                        if( !(PROP_IS_IN_NNF<=subFormulaConds) )
                            mPropositions &= ~PROP_IS_IN_NNF;
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
                            mPropositions &= ~PROP_IS_IN_NNF;
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
                            mPropositions &= ~PROP_IS_IN_NNF;
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
                            mPropositions &= ~PROP_IS_IN_NNF;
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

    void Formula::addConstraintPropositions( const Constraint& _constraint )
    {
        switch( _constraint.lhs().highestDegree() )
        {
            case 0:
                mPropositions |= PROP_CONTAINS_LINEAR_POLYNOMIAL;
                break;
            case 1:
                mPropositions |= PROP_CONTAINS_LINEAR_POLYNOMIAL;
                break;
            case 2:
                mPropositions |= PROP_CONTAINS_NONLINEAR_POLYNOMIAL;
                break;
            case 3:
                mPropositions |= PROP_CONTAINS_NONLINEAR_POLYNOMIAL;
                mPropositions &= ~PROP_VARIABLE_DEGREE_LESS_THAN_THREE;
                break;
            case 4:
                mPropositions |= PROP_CONTAINS_NONLINEAR_POLYNOMIAL;
                mPropositions &= ~PROP_VARIABLE_DEGREE_LESS_THAN_FOUR;
                break;
            case 5:
                mPropositions |= PROP_CONTAINS_NONLINEAR_POLYNOMIAL;
                mPropositions &= ~PROP_VARIABLE_DEGREE_LESS_THAN_FIVE;
                break;
            default:
            {
            }
        }
        switch( _constraint.relation() )
        {
            case Constraint::EQ:
                mPropositions |= PROP_CONTAINS_EQUATION;
                break;
            case Constraint::NEQ:
                mPropositions |= PROP_CONTAINS_STRICT_INEQUALITY;
                break;
            case Constraint::LEQ:
                mPropositions |= PROP_CONTAINS_INEQUALITY;
                break;
            case Constraint::GEQ:
                mPropositions |= PROP_CONTAINS_INEQUALITY;
                break;
            case Constraint::LESS:
                mPropositions |= PROP_CONTAINS_STRICT_INEQUALITY;
                break;
            case Constraint::GREATER:
                mPropositions |= PROP_CONTAINS_STRICT_INEQUALITY;
                break;
            default:
            {
            }
        }
        if( _constraint.hasIntegerValuedVariable() )
            mPropositions |= PROP_CONTAINS_INTEGER_VALUED_VARS;
        if( _constraint.hasRealValuedVariable() )
            mPropositions |= PROP_CONTAINS_REAL_VALUED_VARS;
    }

    string Formula::toString( bool _withActivity, unsigned _resolveUnequal, const string _init, bool _oneline, bool _infix, bool _friendlyNames ) const
    {
        string activity = "";
        if( _withActivity )
        {
            stringstream s;
            s << " [" << mDifficulty << ":" << mActivity << "]";
            activity += s.str();
        }
        if( mType == BOOL )
        {
            return (_init + (*mpIdentifier) + activity);
        }
        else if( mType == CONSTRAINT )
            return (_init + mpConstraint->toString( _resolveUnequal, _infix, _friendlyNames ) + activity);
        else if( isAtom() )
            return (_init + FormulaTypeToString( mType ) + activity);
        else if( mType == NOT )
        {
            string result = _init;
            if( _infix )
            {
                result += "not(";
                if( !_oneline ) result += "\n";
            }
            else
            {
                result += "(not";
                result += (_oneline ? " " : "\n");
            }
            result += (*mpSubformulas->begin())->toString( _withActivity, _resolveUnequal, _oneline ? "" : (_init + "   "), _oneline, _infix, _friendlyNames );
            result += (_oneline ? "" : "\n") + _init + ")";
            return result;
        }
        assert( isBooleanCombination() );
        string stringOfType = FormulaTypeToString( mType );
        string result = _init + "(";
        if( _infix )
        {
            for( auto subformula = mpSubformulas->begin(); subformula != mpSubformulas->end(); ++subformula )
            {
                if( subformula != mpSubformulas->begin() )
                    result += stringOfType;
                if( !_oneline ) 
                    result += "\n";
                result += (*subformula)->toString( _withActivity, _resolveUnequal, _oneline ? "" : (_init + "   "), _oneline, true, _friendlyNames );
            }
        }
        else
        {
            result += stringOfType;
            for( auto subformula = mpSubformulas->begin(); subformula != mpSubformulas->end(); ++subformula )
            {
                result += (_oneline ? " " : "\n");
                result += (*subformula)->toString( _withActivity, _resolveUnequal, _oneline ? "" : (_init + "   "), _oneline, false, _friendlyNames );
            }
        }
        result += ")";
        if( _withActivity )
            result += activity;
        return result;
    }
    
    ostream& operator<<( ostream& _ostream, const Formula& _formula )
    {
        return (_ostream << _formula.toString( false, 0, "", true, false, true ));
    }

    void Formula::printProposition( ostream& _out, const string _init ) const
    {
        _out << _init;
        for( unsigned i = 0; i < proposition().size(); ++i )
        {
            if( fmod( i, 10.0 ) == 0.0 ) 
                _out << " ";
            _out << proposition()[i];
        }
        _out << endl;
    }
    
    std::string Formula::toRedlogFormat( bool _withVariables ) const
    {
        string result = "";
        string oper = Formula::FormulaTypeToString( mType );
        switch( mType )
        {
            // unary cases
            case TTRUE:
                result += " " + oper + " ";
                break;
            case FFALSE:
                result += " " + oper + " ";
                break;
            case NOT:
                result += " " + oper + "( " + (*mpSubformulas->begin())->toRedlogFormat( _withVariables ) + " )";
                break;
            case CONSTRAINT:
                result += constraint().toString( 1 );
                break;
            case BOOL:
                result += *mpIdentifier + " = 1";
                break;
            default:
            {
                // recursive print of the subformulas
                if( _withVariables )
                { // add the variables
                    result += "( ex( {";
                    result += variableListToString( "," );
                    result += "}, (";
                    // Make pseudo Booleans.
                    set<string> boolVars = set<string>();
                    booleanVars( boolVars );
                    for( auto j = boolVars.begin(); j != boolVars.end(); ++j )
                        result += "(" + *j + " = 0 or " + *j + " = 1) and ";
                }
                else
                    result += "( ";
                std::list<Formula*>::const_iterator it = mpSubformulas->begin();
                // do not quantify variables again.
                result += (*it)->toRedlogFormat( false );
                for( ++it; it != mpSubformulas->end(); ++it ) // do not quantify variables again.
                    result += " " + oper + " " + (*it)->toRedlogFormat( false );
                if( _withVariables )
                    result += " ) )";
                result += " )";
            }
        }
        return result;
    }

    std::string Formula::variableListToString( std::string _separator, const unordered_map<string, string>& _variableIds ) const
    {
        Variables realVars = Variables();
        realValuedVars( realVars );
        set<string> boolVars = set<string>();
        booleanVars( boolVars );
        auto i = realVars.begin();
        auto j = boolVars.begin();
        string result = "";
        if( i != realVars.end() )
        {
            std::stringstream sstream;
            sstream << *i;
            unordered_map<string, string>::const_iterator vId = _variableIds.find( sstream.str() );
            result += vId == _variableIds.end() ? sstream.str() : vId->second;
            for( ++i; i != realVars.end(); ++i )
            {
                result += _separator;
                vId = _variableIds.find(sstream.str());
                result += vId == _variableIds.end() ? sstream.str() : vId->second;
            }
        }
        else if( j != boolVars.end() )
        {
            unordered_map<string, string>::const_iterator vId = _variableIds.find(*j);
            result += vId == _variableIds.end() ? *j : vId->second;
            for( ++j; j != boolVars.end(); ++j )
            {
                result += _separator;
                vId = _variableIds.find(*j);
                result += vId == _variableIds.end() ? *j : vId->second;
            }
        }
        return result;
    }

    std::string Formula::FormulaTypeToString( Type _type )
    {
        switch( _type )
        {
            case AND:
                return "and";
            case OR:
                return "or";
            case NOT:
                return "not";
            case IFF:
                return "=";
            case XOR:
                return "xor";
            case IMPLIES:
                return "=>";
            case TTRUE:
                return "true";
            case FFALSE:
                return "false";
            default:
                return "";
        }
    }

    bool Formula::resolveNegation( Formula& _formula, bool _keepConstraint )
    {
        assert( _formula.getType() == NOT );
        Formula* subformula = _formula.back();
        switch( subformula->getType() )
        {
            case BOOL:
                return false;
            case CONSTRAINT:
            {
                if( _keepConstraint )
                    return false;
                else
                {
                    const Constraint* constraint = subformula->pConstraint();
                    _formula.pop_back();
                    switch( constraint->relation() )
                    {
                        case Constraint::EQ:
                            #ifdef REMOVE_UNEQUAL_IN_CNF_TRANSFORMATION
                            _formula.copyAndDelete( new Formula( OR ));
                            _formula.addSubformula( new Formula( Formula::newConstraint( constraint->lhs(), Constraint::LESS )));
                            _formula.addSubformula( new Formula( Formula::newConstraint( -constraint->lhs(), Constraint::LESS )));
                            #else
                            _formula.copyAndDelete( new Formula( Formula::newConstraint( constraint->lhs(), Constraint::NEQ )));
                            #endif
                            return true;
                        case Constraint::LEQ:
                            _formula.copyAndDelete( new Formula( Formula::newConstraint( -constraint->lhs(), Constraint::LESS )));
                            return false;
                        case Constraint::LESS:
                            #ifdef REMOVE_LESS_EQUAL_IN_CNF_TRANSFORMATION
                            _formula.copyAndDelete( new Formula( OR ));
                            _formula.addSubformula( new Formula( Formula::newConstraint( -constraint->lhs(), Constraint::LESS )));
                            _formula.addSubformula( new Formula( Formula::newConstraint( -constraint->lhs(), Constraint::EQ )));
                            return true;
                            #else
                            _formula.copyAndDelete( new Formula( Formula::newConstraint( -constraint->lhs(), Constraint::LEQ )));
                            return false;
                            #endif
                        case Constraint::NEQ:
                            _formula.copyAndDelete( new Formula( Formula::newConstraint( constraint->lhs(), Constraint::EQ )));
                            return false;
                        default:
                            cerr << "Unexpected relation symbol!" << endl;
                            assert( false );
                            return false;
                    }
                }
            }
            case TTRUE: // (not true)  ->  false
                _formula.pop_back();
                _formula.copyAndDelete( new Formula( FFALSE ) );
                return true;
            case FFALSE: // (not false)  ->  true
                _formula.pop_back();
                _formula.copyAndDelete( new Formula( TTRUE ) );
                return true;
            case NOT: // (not (not phi))  ->  phi
            {
                Formula* subsubformula = subformula->pruneBack();
                _formula.pop_back();
                _formula.copyAndDelete( subsubformula );
                return true;
            }
            case AND:
            {
                // (not (and phi_1 .. phi_n))  ->  (or (not phi_1) .. (not phi_n))
                vector<Formula*> subsubformulas = vector<Formula*>();
                while( !subformula->empty() )
                    subsubformulas.push_back( subformula->pruneBack() );
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
                // (not (or phi_1 .. phi_n))  ->  (and (not phi_1) .. (not phi_n))
                vector<Formula*> subsubformulas = vector<Formula*>();
                while( !subformula->empty() )
                    subsubformulas.push_back( subformula->pruneBack() );
                _formula.pop_back();
                _formula.copyAndDelete( new Formula( AND ));
                while( !subsubformulas.empty() )
                {
                    Formula* notFormula = new Formula( NOT );
                    notFormula->addSubformula( subsubformulas.back() );
                    subsubformulas.pop_back();
                    _formula.addSubformula( notFormula );
                }
                return true;
            }
            case IMPLIES:
            {
                assert( subformula->size() == 2 );
                // (not (implies lhs rhs))  ->  (and lhs (not rhs))
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
                // (not (iff lhs rhs))  ->  (xor lhs rhs)
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
                // (not (xor lhs rhs))  ->  (iff lhs rhs)
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
    
    void Formula::toCNF( Formula& _formula, bool _keepConstraints )
    {
        if( _keepConstraints && (_formula.getPropositions() | ~PROP_IS_IN_CNF) == ~PROP_TRUE )
            return;
        else if( _formula.getType() == NOT && (_formula.getPropositions() | ~PROP_IS_IN_CNF) == ~PROP_TRUE )
        {
            resolveNegation( _formula, _keepConstraints );
            return;
        }
        else if( _formula.isAtom() )
            return;
        Formula* copy = new Formula( _formula.getType() );
        while( !_formula.empty() )
            copy->addSubformula( _formula.pruneFront() );
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
                case CONSTRAINT:
                {
                    #ifdef REMOVE_LESS_EQUAL_IN_CNF_TRANSFORMATION
                    const Constraint* constraint = currentFormula->pConstraint();
                    if( constraint->relation() == Constraint::LEQ )
                    {
                        Formula* newFormula = new Formula( OR );
                        newFormula->addSubformula( Formula::newConstraint( constraint->lhs(), Constraint::LESS ) );
                        newFormula->addSubformula( Formula::newConstraint( constraint->lhs(), Constraint::EQ ) );
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
                    // Remove it.
                    delete currentFormula;
                    break;
                }
                case FFALSE:
                {
                    // Makes everything false.
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
                    // Try to resolve this negation.
                    if( !Formula::resolveNegation( *currentFormula, _keepConstraints )) // It is a literal.
                        _formula.addSubformula( currentFormula );
                    else
                        subformulasToTransform.push_back( currentFormula );
                    break;
                }
                case AND:
                {
                    // (and phi_1 .. phi_n) -> psi_1 .. psi_m
                    while( !currentFormula->empty() )
                        subformulasToTransform.push_back( currentFormula->pruneBack() );
                    delete currentFormula;
                    break;
                }
                // Note, that the following case could be implemented using less code, but it would clearly
                // lead to a worse performance as we would then not benefit from the properties of a disjunction.
                case OR:
                {
                    // (or phi_1 .. phi_n) -> (or psi_1 .. psi_m),  where phi_i is transformed as follows:
                    vector<Formula*> phis = vector<Formula*>();
                    while( !currentFormula->empty() )
                        phis.push_back( currentFormula->pruneBack() );
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
                            case CONSTRAINT:
                            {
                                #ifdef REMOVE_LESS_EQUAL_IN_CNF_TRANSFORMATION
                                const Constraint* constraint = currentSubformula->pConstraint();
                                if( constraint->relation() == Constraint::LEQ )
                                {
                                    Formula* newFormula = new Formula( OR );
                                    newFormula->addSubformula( Formula::newConstraint( constraint->lhs(), Constraint::LESS ) );
                                    newFormula->addSubformula( Formula::newConstraint( constraint->lhs(), Constraint::EQ ) );
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
                                // Try to resolve this negation.
                                if( Formula::resolveNegation( *currentSubformula, _keepConstraints ))
                                    phis.push_back( currentSubformula );
                                else // It is a literal.
                                    currentFormula->addSubformula( currentSubformula );
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
                                    phis.push_back( currentSubformula->pruneBack() );
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
                        delete currentFormula;
                    break;
                }
                case IMPLIES:
                {
                    // (-> lhs rhs)  ->  (or (not lhs) rhs)
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
                    // (iff lhs rhs)  ->  (or h1 h2) (or (not h1) lhs) (or (not h1) rhs) (or (not h2) (not lhs)) (or (not h2) (not rhs))
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
                    // (xor lhs rhs)  ->  (or h1 h2) (or (not h1) (not lhs)) (or (not h1) rhs) (or (not h2) lhs) (or (not h2) (not rhs))
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
            _formula.copyAndDelete( new Formula( TTRUE ));
        else if( _formula.isBooleanCombination() && _formula.size() == 1 )
        {
            Formula* subFormula = _formula.pruneBack();
            _formula.copyAndDelete( subFormula );
        }
        _formula.getPropositions();
    }
}    // namespace smtrat

