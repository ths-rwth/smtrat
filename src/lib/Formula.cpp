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
#define REMOVE_UNEQUAL_IN_CNF_TRANSFORMATION

#include "Formula.h"
#include "Module.h"
#include "FormulaPool.h"

using namespace std;

namespace smtrat
{
    Formula::Formula( bool _true, size_t _id ):
        mDeducted( false ),
        mHash( ((size_t)(_true ? constraintPool().consistentConstraint()->id() : constraintPool().inconsistentConstraint()->id())) << (sizeof(size_t)*4) ),
        mId( _id ),
        mActivity( 0 ),
        mDifficulty( 0 ),
        mType( _true ? TTRUE : FFALSE ),
        mpConstraint( _true ? constraintPool().consistentConstraint() : constraintPool().inconsistentConstraint() ),
        mProperties()
    {}
    
    Formula::Formula( const carl::Variable::Arg _boolean ):
        mDeducted( false ),
        mHash( (size_t)_boolean.getId() ), // TODO: subtract the id of the boolean variable with the smallest id
        mId( 0 ),
        mActivity( 0 ),
        mDifficulty( 0 ),
        mType( BOOL ),
        mBoolean( _boolean ),
        mProperties()
    {
        assert( _boolean.getType() == carl::VariableType::VT_BOOL );
    }

    Formula::Formula( const Constraint* _constraint ):
        mDeducted( false ),
        mHash( ((size_t) _constraint->id()) << (sizeof(size_t)*4) ),
        mId( 0 ),
        mActivity( 0 ),
        mDifficulty( 0 ),
        mType( CONSTRAINT ),
        mpConstraint( _constraint ),
        mProperties()
    {
        switch( _constraint->isConsistent() )
        {
            case 0: 
                assert( mpConstraint == constraintPool().inconsistentConstraint() );
                mType = FFALSE;
                break;
            case 1: 
                assert( mpConstraint == constraintPool().consistentConstraint() );
                mType = TTRUE;
                break;
            default:
            {}
        }
    }
         
    Formula::Formula( const Formula* _subformula ):
        mDeducted( false ),
        mHash( ((size_t)NOT << 5) ^ _subformula->getHash() ),
        mId( 0 ),
        mActivity( 0 ),
        mDifficulty( 0 ),
        mType( NOT ),
        mProperties()
    {
        mpSubformula = _subformula;
    }

    Formula::Formula( const Formula* _premise, const Formula* _conclusion ):
        mDeducted( false ),
        mHash( CIRCULAR_SHIFT(size_t, (((size_t)IMPLIES << 5) ^ _premise->getHash()), 5) ^ _conclusion->getHash() ),
        mId( 0 ),
        mActivity( 0 ),
        mDifficulty( 0 ),
        mType( IMPLIES ),
        mProperties()
    {
        mpImpliesContent = new IMPLIESContent( _premise, _conclusion );
    }

    Formula::Formula( const Formula* _conditon, const Formula* _then, const Formula* _else ):
        mDeducted( false ),
        mHash( CIRCULAR_SHIFT(size_t, (CIRCULAR_SHIFT(size_t, (((size_t)ITE << 5) ^ _conditon->getHash()), 5) ^ _then->getHash()), 5) ^ _else->getHash() ),
        mId( 0 ),
        mActivity( 0 ),
        mDifficulty( 0 ),
        mType( ITE ),
        mProperties()
    {
        mpIteContent = new ITEContent( _conditon, _then, _else );
    }
    
    Formula::Formula( Type _type, PointerSet<Formula>&& _subformulas ):
        mDeducted( false ),
        mHash( (size_t)_type ),
        mId( 0 ),
        mActivity( 0 ),
        mDifficulty( 0 ),
        mType( _type ),
        mProperties()
    {
        assert( _subformulas.size() > 1 );
        assert( mType == AND || mType == OR || mType == IFF || mType == XOR );
        mpSubformulas = new PointerSet<Formula>( move( _subformulas ) );
        for( const Formula* subformula : *mpSubformulas )
        {
            mHash = CIRCULAR_SHIFT(size_t, mHash, 5);
            mHash ^= subformula->getHash();
        }
    }

    Formula::~Formula()
    {
        if( isNary() )
        {
            mpSubformulas->clear();
            delete mpSubformulas;
        }
        else if( mType == CONSTRAINT )
        {
            mpConstraint = NULL;
        }
        else if( mType == NOT )
        {
            mpSubformula = NULL;
        }
        else if( mType == IMPLIES )
        {
            delete mpImpliesContent;
        }
        else if( mType == ITE )
        {
            delete mpIteContent;
        }
    }
    
    void Formula::collectVariables( Variables& _vars, carl::VariableType _type, bool _ofThisType ) const
    {
        switch( mType )
        {
            case BOOL:
                if( _ofThisType == (_type == carl::VariableType::VT_BOOL) )
                {
                    _vars.insert( mBoolean );
                }
                break;
            case TTRUE:
                break;
            case FFALSE:
                break;
            case CONSTRAINT:
                if( !(_ofThisType && _type == carl::VariableType::VT_BOOL) ) // NOTE: THIS ASSUMES THAT THE VARIABLES IN THE CONSTRAINT HAVE INFINTE DOMAINS
                {
                    for( auto var : mpConstraint->variables() )
                    {
                        if( _ofThisType == (var.getType() == carl::VariableType::VT_INT) )
                            _vars.insert( var );
                        if( _ofThisType == (var.getType() == carl::VariableType::VT_REAL) )
                            _vars.insert( var );
                    }
                }
                break;
            case NOT:
                mpSubformula->collectVariables( _vars, _type, _ofThisType );
                break;
            case IMPLIES:
                premise().collectVariables( _vars, _type, _ofThisType );
                conclusion().collectVariables( _vars, _type, _ofThisType );
                break;
            case ITE:
                condition().collectVariables( _vars, _type, _ofThisType );
                firstCase().collectVariables( _vars, _type, _ofThisType );
                secondCase().collectVariables( _vars, _type, _ofThisType );
                break;
            default:
            {
                for( const Formula* subform : *mpSubformulas )
                    subform->collectVariables( _vars, _type, _ofThisType );
            }
        }
    }
    
    bool Formula::operator==( const Formula& _formula ) const
    {
        if( mId == 0 || _formula.getId() == 0 )
        {
            if( mType != _formula.getType() )
                return false;
            switch( mType )
            {
                case BOOL:
                    return mBoolean == _formula.boolean();
                case TTRUE:
                    return true;
                case FFALSE:
                    return true;
                case CONSTRAINT:
                    return (*mpConstraint) == _formula.constraint();
                case NOT:
                    return (*mpSubformula) == _formula.subformula();
                case IMPLIES:
                    return (*mpImpliesContent->mpPremise) == _formula.premise() && (*mpImpliesContent->mpConlusion) == _formula.conclusion();
                case ITE:
                    return (*mpIteContent->mpCondition) == _formula.condition()
                            && (*mpIteContent->mpThen) == _formula.firstCase()
                            && (*mpIteContent->mpElse) == _formula.secondCase();
                default:
                    return (*mpSubformulas) == _formula.subformulas();
            }
        }
        else
            return mId == _formula.getId();
    }
    
    unsigned Formula::satisfiedBy( const EvalRationalMap& _assignment ) const
    {
        switch( mType )
        {
            case TTRUE:
            {
                return 1;
            }
            case FFALSE:
            {
                return 0;
            }
            case BOOL:
            {
                auto ass = _assignment.find( mBoolean );
                return ass == _assignment.end() ? 2 : (ass->second == ONE_RATIONAL ? 1 : 0);
            }
            case CONSTRAINT:
            {
                return mpConstraint->satisfiedBy( _assignment );
            }
            case NOT:
            {
                switch( mpSubformula->satisfiedBy( _assignment ) )
                {
                    case 0:
                        return 1;
                    case 1:
                        return 0;
                    default:
                        return 2;
                }   
            }
            case OR:
            {
                unsigned result = 0;
                for( auto subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
                {
                    switch( (*subFormula)->satisfiedBy( _assignment ) )
                    {
                        case 0:
                            break;
                        case 1:
                            return 1;
                        default:
                            if( result != 2 ) result = 2;
                    }
                }
                return result;
            }
            case AND:
            {
                unsigned result = 1;
                for( auto subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
                {
                    switch( (*subFormula)->satisfiedBy( _assignment ) )
                    {
                        case 0:
                            return 0;
                        case 1:
                            break;
                        default:
                            if( result != 2 ) result = 2;
                    }
                }
                return result;
            }
            case IMPLIES:
            {
                unsigned result = premise().satisfiedBy( _assignment );
                if( result == 0 ) return 1;
                switch( conclusion().satisfiedBy( _assignment ) )
                {
                    case 0:
                        return result == 1 ? 0 : 2;
                    case 1:
                        return 1;
                    default:
                        return 2;
                }
            }
            case ITE:
            {
                unsigned result = condition().satisfiedBy( _assignment );
                switch( result )
                {
                    case 0:
                        return secondCase().satisfiedBy( _assignment );
                    case 1:
                        return firstCase().satisfiedBy( _assignment );
                    default:
                        return 2;
                }
            }
            case IFF:
            {
                auto subFormula = mpSubformulas->begin();
                unsigned result = (*subFormula)->satisfiedBy( _assignment );
                bool containsTrue = (result == 1 ? true : false);
                bool containsFalse = (result == 0 ? true : false);
                ++subFormula;
                while( subFormula != mpSubformulas->end() )
                {
                    unsigned resultTmp = (*subFormula)->satisfiedBy( _assignment );
                    switch( resultTmp )
                    {
                        case 0:
                            containsFalse = true;
                            break;
                        case 1:
                            containsTrue = true;
                        default:
                            result = 2;
                    }
                    if( containsFalse && containsTrue )
                        return 0;
                    ++subFormula;
                }
                return (result == 2 ? 2 : 1);
            }
            case XOR:
            {
                auto subFormula = mpSubformulas->begin();
                unsigned result = (*subFormula)->satisfiedBy( _assignment );
                if( result == 2 ) return 2;
                ++subFormula;
                while( subFormula != mpSubformulas->end() )
                {
                    unsigned resultTmp = (*subFormula)->satisfiedBy( _assignment );
                    if( resultTmp == 2 ) return 2;
                    result = resultTmp != result;
                    ++subFormula;
                }
                return result;
            }
            default:
            {
                assert( false );
                cerr << "Undefined operator!" << endl;
                return 2;
            }
        }
    }
    
    unsigned Formula::satisfiedBy( const Model& _assignment ) const
    {
        EvalRationalMap rationalAssigns;
        if( getRationalAssignmentsFromModel( _assignment, rationalAssigns ) )
            return satisfiedBy( rationalAssigns );
        else
            return 2; // TODO: Check also models having square roots as value.
    }
    
    void Formula::initProperties()
    {
        mProperties = Condition();
        switch( mType )
        {
            case TTRUE:
            {
                mProperties |= STRONG_CONDITIONS;
                addConstraintProperties( *mpConstraint );
                break;
            }
            case FFALSE:
            {
                mProperties |= STRONG_CONDITIONS;
                addConstraintProperties( *mpConstraint );
                break;
            }
            case BOOL:
            {
                mProperties |= STRONG_CONDITIONS | PROP_CONTAINS_BOOLEAN;
                break;
            }
            case CONSTRAINT:
            {
                mProperties |= STRONG_CONDITIONS;
                addConstraintProperties( *mpConstraint );
                break;
            }
            case NOT:
            {
                Condition subFormulaConds = mpSubformula->properties();
                if( PROP_IS_AN_ATOM <= subFormulaConds )
                    mProperties |= PROP_IS_A_CLAUSE | PROP_IS_A_LITERAL | PROP_IS_IN_CNF | PROP_IS_PURE_CONJUNCTION;
                mProperties |= (subFormulaConds & PROP_VARIABLE_DEGREE_LESS_THAN_THREE);
                mProperties |= (subFormulaConds & PROP_VARIABLE_DEGREE_LESS_THAN_FOUR);
                mProperties |= (subFormulaConds & PROP_VARIABLE_DEGREE_LESS_THAN_FIVE);
                mProperties |= (subFormulaConds & WEAK_CONDITIONS);
                break;
            }
            case OR:
            {
                mProperties |= PROP_IS_A_CLAUSE | PROP_IS_IN_CNF | PROP_IS_IN_NNF;
                mProperties |= PROP_VARIABLE_DEGREE_LESS_THAN_THREE | PROP_VARIABLE_DEGREE_LESS_THAN_FOUR | PROP_VARIABLE_DEGREE_LESS_THAN_FIVE;
                for( auto subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
                {
                    Condition subFormulaConds = (*subFormula)->properties();
                    if( !(PROP_IS_A_LITERAL<=subFormulaConds) )
                    {
                        mProperties &= ~PROP_IS_A_CLAUSE;
                        mProperties &= ~PROP_IS_IN_CNF;
                    }
                    if( !(PROP_IS_IN_NNF<=subFormulaConds) )
                        mProperties &= ~PROP_IS_IN_NNF;
                    mProperties |= (subFormulaConds & WEAK_CONDITIONS);
                }
                break;
            }
            case AND:
            {
                mProperties |= PROP_IS_PURE_CONJUNCTION | PROP_IS_IN_CNF | PROP_IS_IN_NNF;
                mProperties |= PROP_VARIABLE_DEGREE_LESS_THAN_THREE | PROP_VARIABLE_DEGREE_LESS_THAN_FOUR | PROP_VARIABLE_DEGREE_LESS_THAN_FIVE;
                for( auto subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
                {
                    Condition subFormulaConds = (*subFormula)->properties();
                    if( !(PROP_IS_A_CLAUSE<=subFormulaConds) )
                    {
                        mProperties &= ~PROP_IS_PURE_CONJUNCTION;
                        mProperties &= ~PROP_IS_IN_CNF;
                    }
                    else if( !(PROP_IS_A_LITERAL<=subFormulaConds) )
                        mProperties &= ~PROP_IS_PURE_CONJUNCTION;
                    if( !(PROP_IS_IN_NNF<=subFormulaConds) )
                        mProperties &= ~PROP_IS_IN_NNF;
                    mProperties |= (subFormulaConds & WEAK_CONDITIONS);
                }
                break;
            }
            case IMPLIES:
            {
                mProperties |= PROP_IS_IN_NNF;
                mProperties |= PROP_VARIABLE_DEGREE_LESS_THAN_THREE | PROP_VARIABLE_DEGREE_LESS_THAN_FOUR | PROP_VARIABLE_DEGREE_LESS_THAN_FIVE;
                Condition subFormulaCondsA = premise().properties();
                if( !(PROP_IS_IN_NNF<=subFormulaCondsA) )
                    mProperties &= ~PROP_IS_IN_NNF;
                mProperties |= (subFormulaCondsA & WEAK_CONDITIONS);
                Condition subFormulaCondsB = conclusion().properties();
                if( !(PROP_IS_IN_NNF<=subFormulaCondsB) )
                    mProperties &= ~PROP_IS_IN_NNF;
                mProperties |= (subFormulaCondsB & WEAK_CONDITIONS);
                break;
            }
            case ITE:
            {
                mProperties |= PROP_VARIABLE_DEGREE_LESS_THAN_THREE | PROP_VARIABLE_DEGREE_LESS_THAN_FOUR | PROP_VARIABLE_DEGREE_LESS_THAN_FIVE;
                mProperties |= (condition().properties() & WEAK_CONDITIONS);
                mProperties |= (firstCase().properties() & WEAK_CONDITIONS);
                mProperties |= (secondCase().properties() & WEAK_CONDITIONS);
                break;
            }
            case IFF:
            {
                mProperties |= PROP_IS_IN_NNF;
                mProperties |= PROP_VARIABLE_DEGREE_LESS_THAN_THREE | PROP_VARIABLE_DEGREE_LESS_THAN_FOUR | PROP_VARIABLE_DEGREE_LESS_THAN_FIVE;
                for( auto subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
                {
                    Condition subFormulaConds = (*subFormula)->properties();
                    if( !(PROP_IS_IN_NNF<=subFormulaConds) )
                        mProperties &= ~PROP_IS_IN_NNF;
                    mProperties |= (subFormulaConds & WEAK_CONDITIONS);
                }
                break;
            }
            case XOR:
            {
                mProperties |= PROP_IS_IN_NNF;
                mProperties |= PROP_VARIABLE_DEGREE_LESS_THAN_THREE | PROP_VARIABLE_DEGREE_LESS_THAN_FOUR | PROP_VARIABLE_DEGREE_LESS_THAN_FIVE;
                for( auto subFormula = mpSubformulas->begin(); subFormula != mpSubformulas->end(); ++subFormula )
                {
                    Condition subFormulaConds = (*subFormula)->properties();
                    if( !(PROP_IS_IN_NNF<=subFormulaConds) )
                        mProperties &= ~PROP_IS_IN_NNF;
                    mProperties |= (subFormulaConds & WEAK_CONDITIONS);
                }
                break;
            }
            default:
            {
                assert( false );
                cerr << "Undefined operator!" << endl;
            }
        }
    }
    
    void Formula::addConstraintProperties( const Constraint& _constraint )
    {
        switch( _constraint.lhs().totalDegree() )
        {
            case 0:
                mProperties |= PROP_CONTAINS_LINEAR_POLYNOMIAL;
                break;
            case 1:
                mProperties |= PROP_CONTAINS_LINEAR_POLYNOMIAL;
                break;
            case 2:
                mProperties |= PROP_CONTAINS_NONLINEAR_POLYNOMIAL;
                break;
            case 3:
                mProperties |= PROP_CONTAINS_NONLINEAR_POLYNOMIAL;
                mProperties &= ~PROP_VARIABLE_DEGREE_LESS_THAN_THREE;
                break;
            case 4:
                mProperties |= PROP_CONTAINS_NONLINEAR_POLYNOMIAL;
                mProperties &= ~PROP_VARIABLE_DEGREE_LESS_THAN_FOUR;
                break;
            case 5:
                mProperties |= PROP_CONTAINS_NONLINEAR_POLYNOMIAL;
                mProperties &= ~PROP_VARIABLE_DEGREE_LESS_THAN_FIVE;
                break;
            default:
            {
            }
        }
        switch( _constraint.relation() )
        {
            case Relation::EQ:
                mProperties |= PROP_CONTAINS_EQUATION;
                break;
            case Relation::NEQ:
                mProperties |= PROP_CONTAINS_STRICT_INEQUALITY;
                break;
            case Relation::LEQ:
                mProperties |= PROP_CONTAINS_INEQUALITY;
                break;
            case Relation::GEQ:
                mProperties |= PROP_CONTAINS_INEQUALITY;
                break;
            case Relation::LESS:
                mProperties |= PROP_CONTAINS_STRICT_INEQUALITY;
                break;
            case Relation::GREATER:
                mProperties |= PROP_CONTAINS_STRICT_INEQUALITY;
                break;
            default:
            {
            }
        }
        if( _constraint.hasIntegerValuedVariable() )
            mProperties |= PROP_CONTAINS_INTEGER_VALUED_VARS;
        if( _constraint.hasRealValuedVariable() )
            mProperties |= PROP_CONTAINS_REAL_VALUED_VARS;
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
            return (_init + constraintPool().getVariableName( mBoolean, _friendlyNames ) + activity);
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
            result += mpSubformula->toString( _withActivity, _resolveUnequal, _oneline ? "" : (_init + "   "), _oneline, _infix, _friendlyNames );
            result += (_oneline ? "" : "\n") + _init + ")";
            return result;
        }
        else if( mType == IMPLIES )
        {
            string result = _init + "(";
            if( _infix )
            {
                if( !_oneline ) 
                    result += "\n";
                result += premise().toString( _withActivity, _resolveUnequal, _oneline ? "" : (_init + "   "), _oneline, true, _friendlyNames );
                result += " " + FormulaTypeToString( IMPLIES ) + " ";
                if( !_oneline ) 
                    result += "\n";
                result += conclusion().toString( _withActivity, _resolveUnequal, _oneline ? "" : (_init + "   "), _oneline, true, _friendlyNames );
            }
            else
            {
                result += FormulaTypeToString( IMPLIES );
                result += (_oneline ? " " : "\n");
                result += premise().toString( _withActivity, _resolveUnequal, _oneline ? "" : (_init + "   "), _oneline, false, _friendlyNames );
                result += (_oneline ? " " : "\n");
                result += conclusion().toString( _withActivity, _resolveUnequal, _oneline ? "" : (_init + "   "), _oneline, false, _friendlyNames );
            }
            result += ")";
            if( _withActivity )
                result += activity;
            return result;
        }
        else if( mType == ITE )
        {
            string result = _init + "(";
            if( _infix )
            {
                if( !_oneline ) 
                    result += "\n";
                result += condition().toString( _withActivity, _resolveUnequal, _oneline ? "" : (_init + "   "), _oneline, true, _friendlyNames );
                result += " " + FormulaTypeToString( ITE ) + " ";
                if( !_oneline ) 
                    result += "\n";
                result += firstCase().toString( _withActivity, _resolveUnequal, _oneline ? "" : (_init + "   "), _oneline, true, _friendlyNames );
                if( !_oneline ) 
                    result += "\n";
                result += secondCase().toString( _withActivity, _resolveUnequal, _oneline ? "" : (_init + "   "), _oneline, true, _friendlyNames );
            }
            else
            {
                result += FormulaTypeToString( ITE );
                result += (_oneline ? " " : "\n");
                result += condition().toString( _withActivity, _resolveUnequal, _oneline ? "" : (_init + "   "), _oneline, false, _friendlyNames );
                result += (_oneline ? " " : "\n");
                result += firstCase().toString( _withActivity, _resolveUnequal, _oneline ? "" : (_init + "   "), _oneline, false, _friendlyNames );
                result += (_oneline ? " " : "\n");
                result += secondCase().toString( _withActivity, _resolveUnequal, _oneline ? "" : (_init + "   "), _oneline, false, _friendlyNames );
            }
            result += ")";
            if( _withActivity )
                result += activity;
            return result;
        }
        assert( mType == AND || mType == OR || mType == IFF || mType == XOR );
        string stringOfType = FormulaTypeToString( mType );
        string result = _init + "(";
        if( _infix )
        {
            for( auto subformula = mpSubformulas->begin(); subformula != mpSubformulas->end(); ++subformula )
            {
                if( subformula != mpSubformulas->begin() )
                    result += " " + stringOfType + " ";
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
        for( unsigned i = 0; i < properties().size(); ++i )
        {
            if( fmod( i, 10.0 ) == 0.0 ) 
                _out << " ";
            _out << properties()[i];
        }
        _out << endl;
    }
    
    string Formula::toRedlogFormat( bool _withVariables ) const
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
                result += " " + oper + "( " + mpSubformula->toRedlogFormat( _withVariables ) + " )";
                break;
            case CONSTRAINT:
                result += constraint().toString( 1 );
                break;
            case BOOL:
                result += constraintPool().getVariableName( mBoolean, true ) + " = 1";
                break;
            case IMPLIES:
                result += "( " + premise().toRedlogFormat( _withVariables ) + " " + oper + " " + premise().toRedlogFormat( _withVariables ) + " )";
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
                    set<carl::Variable> boolVars = set<carl::Variable>();
                    booleanVars( boolVars );
                    for( auto j = boolVars.begin(); j != boolVars.end(); ++j )
                    {
                        string boolName = constraintPool().getVariableName( *j, true );
                        result += "(" + boolName + " = 0 or " + boolName + " = 1) and ";
                    }
                }
                else
                    result += "( ";
                PointerSet<Formula>::const_iterator it = mpSubformulas->begin();
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

    string Formula::variableListToString( string _separator, const unordered_map<string, string>& _variableIds ) const
    {
        Variables realVars = Variables();
        realValuedVars( realVars );
        set<carl::Variable> boolVars = set<carl::Variable>();
        booleanVars( boolVars );
        auto i = realVars.begin();
        auto j = boolVars.begin();
        string result = "";
        if( i != realVars.end() )
        {
            stringstream sstream;
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
            string boolName = constraintPool().getVariableName( *j, true );
            unordered_map<string, string>::const_iterator vId = _variableIds.find(boolName);
            result += vId == _variableIds.end() ? boolName : vId->second;
            for( ++j; j != boolVars.end(); ++j )
            {
                boolName = constraintPool().getVariableName( *j, true );
                result += _separator;
                vId = _variableIds.find(boolName);
                result += vId == _variableIds.end() ? boolName : vId->second;
            }
        }
        return result;
    }

    string Formula::FormulaTypeToString( Type _type )
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
            case ITE:
                return "ite";
            case TTRUE:
                return "true";
            case FFALSE:
                return "false";
            default:
                return "";
        }
    }

    const Formula* Formula::resolveNegation( bool _keepConstraint ) const
    {
        if( mType != NOT ) return this;
        Type newType = mType;
        switch( mpSubformula->getType() )
        {
            case BOOL:
                return this;
            case CONSTRAINT:
            {
                if( _keepConstraint )
                    return this;
                else
                {
                    const Constraint* constraint = mpSubformula->pConstraint();
                    switch( constraint->relation() )
                    {
                        case Relation::EQ:
                        {
                            #ifdef REMOVE_UNEQUAL_IN_CNF_TRANSFORMATION
                            PointerSet<Formula> subformulas;
                            subformulas.insert( newFormula( newConstraint( constraint->lhs(), Relation::LESS ) ) );
                            subformulas.insert( newFormula( newConstraint( -constraint->lhs(), Relation::LESS ) ) );
                            return newFormula( OR, move( subformulas ) );
                            #else
                            return newFormula( newConstraint( constraint->lhs(), Relation::NEQ ) );
                            #endif
                        }
                        case Relation::LEQ:
                        {
                            return newFormula( newConstraint( -constraint->lhs(), Relation::LESS ) );
                        }
                        case Relation::LESS:
                        {
                            #ifdef REMOVE_LESS_EQUAL_IN_CNF_TRANSFORMATION
                            PointerSet<Formula> subformulas;
                            subformulas.insert( newFormula( newConstraint( -constraint->lhs(), Relation::LESS ) ) );
                            subformulas.insert( newFormula( newConstraint( -constraint->lhs(), Relation::EQ ) ) );
                            return newFormula( OR, move( subformulas ) );
                            #else
                            return newFormula( newConstraint( -constraint->lhs(), Relation::LEQ ) );
                            #endif
                        }
                        case Relation::GEQ:
                        {
                            return newFormula( newConstraint( constraint->lhs(), Relation::LESS ) );
                        }
                        case Relation::GREATER:
                        {
                            #ifdef REMOVE_LESS_EQUAL_IN_CNF_TRANSFORMATION
                            PointerSet<Formula> subformulas;
                            subformulas.insert( newFormula( newConstraint( constraint->lhs(), Relation::LESS ) ) );
                            subformulas.insert( newFormula( newConstraint( constraint->lhs(), Relation::EQ ) ) );
                            return newFormula( OR, move( subformulas ) );
                            #else
                            return newFormula( newConstraint( constraint->lhs(), Relation::LEQ ) );
                            #endif
                        }
                        case Relation::NEQ:
                        {
                            return newFormula( newConstraint( constraint->lhs(), Relation::EQ ) );
                        }
                        default:
                        {
                            assert( false );
                            cerr << "Unexpected relation symbol!" << endl;
                            return this;
                        }
                    }
                }
            }
            case TTRUE: // (not true)  ->  false
                return falseFormula();
            case FFALSE: // (not false)  ->  true
                return trueFormula();
            case NOT: // (not (not phi))  ->  phi
                return mpSubformula->pSubformula();
            case IMPLIES:
            {
                assert( mpSubformula->size() == 2 );
                // (not (implies lhs rhs))  ->  (and lhs (not rhs))
                PointerSet<Formula> subformulas;
                subformulas.insert( mpSubformula->pPremise() );
                subformulas.insert( newNegation( mpSubformula->pConclusion() ) );
                return newFormula( AND, move( subformulas ) );
            }
            case ITE: // (not (ite cond then else))  ->  (ite cond (not then) (not else))
            {
                return newIte( mpSubformula->pCondition(), newNegation( mpSubformula->pFirstCase() ), newNegation( mpSubformula->pSecondCase() ) );
            }
            case IFF: // (not (iff phi_1 .. phi_n))  ->  (and (or phi_1 .. phi_n) (or (not phi_1) .. (not phi_n)))
            {
                PointerSet<Formula> subformulasA;
                PointerSet<Formula> subformulasB;
                for( auto subformula : mpSubformula->subformulas() )
                {
                    subformulasA.insert( subformula );
                    subformulasB.insert( newNegation( subformula ) );
                }
                return newFormula( AND, newFormula( OR, move( subformulasA ) ), newFormula( OR, move( subformulasB ) ) );
            }
            case XOR: // (not (xor phi_1 .. phi_n))  ->  (xor (not phi_1) phi_2 .. phi_n)
            {
                auto subformula = mpSubformula->subformulas().begin();
                PointerSet<Formula> subformulas;
                subformulas.insert( newNegation( *subformula ) );
                ++subformula;
                for( ; subformula != mpSubformula->subformulas().end(); ++subformula )
                    subformulas.insert( *subformula );
                return newFormula( XOR, move( subformulas ) );
            }
            case AND: // (not (and phi_1 .. phi_n))  ->  (or (not phi_1) .. (not phi_n))
                newType = OR;
                break;
            case OR: // (not (or phi_1 .. phi_n))  ->  (and (not phi_1) .. (not phi_n))
                newType = AND;
                break;
            default:
                assert( false );
                cerr << "Unexpected type of formula!" << endl;
                return this;
        }
        assert( newType != mpSubformula->getType() );
        assert( mpSubformula->getType() == AND || mpSubformula->getType() == OR );
        PointerSet<Formula> subformulas;
        for( const Formula* subsubformula : mpSubformula->subformulas() )
            subformulas.insert( newNegation( subsubformula ) );
        return newFormula( newType, move( subformulas ) );
    }
    
    const Formula* Formula::connectPrecedingSubformulas() const
    {
        assert( isNary() );
        if( mpSubformulas->size() > 2 )
        {
            PointerSet<Formula> tmpSubformulas;
            auto iter = mpSubformulas->rbegin();
            ++iter;
            for( ; iter != mpSubformulas->rend(); ++iter )
                tmpSubformulas.insert( *iter );
            return newFormula( mType, tmpSubformulas );
        }
        else
        {
            assert( mpSubformulas->size() == 2 );
            return *(mpSubformulas->begin());
        }
    }
    
    const Formula* Formula::toCNF( bool _keepConstraints ) const
    {
        if( propertyHolds( PROP_IS_IN_CNF ) )
        {
            if( _keepConstraints )
                return this;
            else if( mType == NOT )
            {
                assert( propertyHolds( PROP_IS_A_LITERAL ) );
                return resolveNegation( _keepConstraints );
            }
        }
        else if( isAtom() )
            return this;
        PointerMap<Formula,pair<const Formula*,const Formula*>*> tseitinVars;
        PointerSet<Formula> subformulas;
        vector<const Formula*> subformulasToTransform;
        subformulasToTransform.push_back( this );
        while( !subformulasToTransform.empty() )
        {
            const Formula* currentFormula = subformulasToTransform.back();
//            cout << "To add:" << endl;
//            for( auto f : subformulasToTransform )
//                cout << "   " << *f << endl;
//            cout << endl;
//            cout << "Conjunction:" << endl;
//            for( auto f : subformulas )
//                cout << "   " << *f << endl;
//            cout << endl;
            subformulasToTransform.pop_back();
            switch( currentFormula->getType() )
            {
                case BOOL:
                {
                    subformulas.insert( currentFormula );
                    break;
                }
                case CONSTRAINT:
                {
                    #ifdef REMOVE_LESS_EQUAL_IN_CNF_TRANSFORMATION
                    if( currentFormula->constraint().relation() == Relation::LEQ )
                    {
                        const Constraint* c1 = newConstraint( currentFormula->constraint().lhs(), Relation::LESS );
                        const Constraint* c2 = newConstraint( currentFormula->constraint().lhs(), Relation::EQ );
                        subformulasToTransform.push_back( newFormula( OR, newFormula( c1 ), newFormula( c2 ) ) );
                    }
                    else
                    {
                    #endif
                    #ifdef REMOVE_UNEQUAL_IN_CNF_TRANSFORMATION
                    if( currentFormula->constraint().relation() == Relation::NEQ )
                    {
                        const Constraint* c1 =  newConstraint( currentFormula->constraint().lhs(), Relation::LESS );
                        const Constraint* c2 =  newConstraint( -currentFormula->constraint().lhs(), Relation::LESS );
                        subformulasToTransform.push_back( newFormula( OR, newFormula( c1 ), newFormula( c2 ) ) );
                    }
                    else
                    {
                    #endif
                    subformulas.insert( currentFormula );
                    #ifdef REMOVE_UNEQUAL_IN_CNF_TRANSFORMATION
                    }
                    #endif
                    #ifdef REMOVE_LESS_EQUAL_IN_CNF_TRANSFORMATION
                    }
                    #endif
                    break;
                }
                case TTRUE: // Remove it.
                    break;
                case FFALSE: // Return false.
                    goto ReturnFalse;
                case NOT: // Try to resolve this negation.
                {
                    const Formula* resolvedFormula = currentFormula->resolveNegation( _keepConstraints );
                    if( resolvedFormula == currentFormula ) // It is a literal.
                        subformulas.insert( currentFormula );
                    else
                        subformulasToTransform.push_back( resolvedFormula );
                    break;
                }
                case AND: // (and phi_1 .. phi_n) -> psi_1 .. psi_m
                {
                    for( const Formula* subformula : currentFormula->subformulas() )
                        subformulasToTransform.push_back( subformula );
                    break;
                }
                case IMPLIES: // (-> lhs rhs)  ->  (or (not lhs) rhs)
                {
                    PointerSet<Formula> tmpSubformulas;
                    tmpSubformulas.insert( newNegation( currentFormula->pPremise() ) );
                    tmpSubformulas.insert( currentFormula->pConclusion() );
                    subformulasToTransform.push_back( newFormula( OR, tmpSubformulas ) );
                    break;
                }
                case ITE: // (ite cond then else)  ->  auxBool, where (or (not cond) (= auxBool then)) and (or cond (= auxBool else)) are added to the queue
                {
                    const Formula* auxBool = newFormula( newAuxiliaryBooleanVariable() );
                    // Add: (or (not cond) (= auxBool then))
                    subformulasToTransform.push_back( newFormula( OR, newNegation( currentFormula->pCondition() ), newFormula( IFF, auxBool, currentFormula->pFirstCase() ) ) );
                    // Add: (or cond (= auxBool else))
                    subformulasToTransform.push_back( newFormula( OR, currentFormula->pCondition(), newFormula( IFF, auxBool, currentFormula->pSecondCase() ) ) );
                    // Add: auxBool
                    subformulas.insert( auxBool );
                    break;
                }
                case IFF: 
                {
                    if( currentFormula->subformulas().size() > 2 )
                    {
                        // (iff phi_1 .. phi_n) -> (or (and phi_1 .. phi_n) (and (not phi_1) .. (not phi_n))) is added to the queue
                        PointerSet<Formula> subformulasA;
                        PointerSet<Formula> subformulasB;
                        for( auto subformula : currentFormula->subformulas() )
                        {
                            subformulasA.insert( subformula );
                            subformulasB.insert( newNegation( subformula ) );
                        }
                        subformulasToTransform.push_back( newFormula( OR, newFormula( AND, move( subformulasA ) ), newFormula( AND, move( subformulasB ) ) ) );
                    }
                    else
                    {
                        // (iff lhs rhs) -> (or lhs (not rhs)) and (or (not lhs) rhs) are added to the queue
                        assert( currentFormula->subformulas().size() == 2 );
                        // Get lhs and rhs.
                        const Formula* lhs = *currentFormula->subformulas().begin();
                        const Formula* rhs = currentFormula->back();
                        // add (or lhs (not rhs)) to the queue
                        subformulasToTransform.push_back( newFormula( OR, lhs, newNegation( rhs ) ) );
                        // add (or (not lhs) rhs) to the queue
                        subformulasToTransform.push_back( newFormula( OR, newNegation( lhs ), rhs ) );
                    }
                    break;
                }
                case XOR: // (xor lhs rhs) -> (or lhs rhs) and (or (not lhs) (not rhs)) are added to the queue
                {
                    // Get lhs and rhs.
                    const Formula* lhs = currentFormula->connectPrecedingSubformulas();
                    const Formula* rhs = currentFormula->back();
                    // add (or lhs rhs) to the queue
                    subformulasToTransform.push_back( newFormula( OR, lhs, rhs) );
                    // add (or (not lhs) (not rhs)) to the queue
                    subformulasToTransform.push_back( newFormula( OR, newNegation( lhs ), newNegation( rhs ) ) );
                    break;
                }
                // Note, that the following case could be implemented using less code, but it would clearly
                // lead to a worse performance as we would then not benefit from the properties of a disjunction.
                case OR: // (or phi_1 .. phi_n) -> (or psi_1 .. psi_m),  where phi_i is transformed as follows:
                {
                    bool currentFormulaValid = false;
                    PointerSet<Formula> subsubformulas;
                    vector<const Formula*> phis;
                    for( const Formula* subformula : currentFormula->subformulas() )
                        phis.push_back( subformula );
                    vector<const Formula*> subformulasToTransformTmp;
                    while( !currentFormulaValid && !phis.empty() )
                    {
                        const Formula* currentSubformula = phis.back();
//                        cout << "    To add:" << endl;
//                        for( auto f : phis )
//                            cout << "       " << *f << endl;
//                        cout << endl;
//                        cout << "    Disjunction:" << endl;
//                        for( auto f : subsubformulas )
//                            cout << "       " << *f << endl;
//                        cout << endl;
                        phis.pop_back();
                        switch( currentSubformula->getType() )
                        {
                            case BOOL: // B -> B
                                subsubformulas.insert( currentSubformula );
                                break;
                            case TTRUE: // remove the entire considered disjunction and everything which has been created by considering it
                                currentFormulaValid = true;
                                break;
                            case FFALSE: // remove it
                                break;
                            case OR: // (or phi_i1 .. phi_ik) -> phi_i1 .. phi_ik
                                for( const Formula* subsubformula : currentSubformula->subformulas() )
                                    phis.push_back( subsubformula );
                                break;
                            case IMPLIES: // (-> lhs_i rhs_i) -> (not lhs_i) rhs_i
                                phis.push_back( newNegation( currentSubformula->pPremise() ) );
                                phis.push_back( currentSubformula->pConclusion() );
                                break;
                            case ITE: // (ite cond then else)  ->  (and (or (not cond) (= auxBool then)) (or cond (= auxBool else) auxBool)
                            {   
                                const Formula* auxBool = newFormula( newAuxiliaryBooleanVariable() );
                                PointerSet<Formula> tmpSubformulas;
                                // Add: (or (not cond) (= auxBool then))
                                tmpSubformulas.insert( newFormula( OR, newNegation( currentSubformula->pCondition() ), newFormula( IFF, auxBool, currentSubformula->pFirstCase() ) ) );
                                // Add: (or cond (= auxBool else))
                                tmpSubformulas.insert( newFormula( OR, currentSubformula->pCondition(), newFormula( IFF, auxBool, currentSubformula->pSecondCase() ) ) );
                                // Add: auxBool
                                tmpSubformulas.insert( auxBool );
                                phis.push_back( newFormula( AND, tmpSubformulas ) );
                                break;
                            }
                            case NOT: // resolve the negation
                            {
                                const Formula* resolvedFormula = currentSubformula->resolveNegation( _keepConstraints );
                                if( resolvedFormula == currentSubformula ) // It is a literal.
                                    subsubformulas.insert( currentSubformula );
                                else
                                    phis.push_back( resolvedFormula );
                                break;
                            }
                            case AND: // (and phi_i1 .. phi_ik) -> h_i, where (or (not h_i) phi_i1) .. (or (not h_i) phi_ik) is added to the queue
                            {
                                auto iter = tseitinVars.insert( pair<const Formula*,pair<const Formula*,const Formula*>*>( currentSubformula, NULL ) );
                                if( iter.second )
                                {
                                    carl::Variable auxVar = newAuxiliaryBooleanVariable();
                                    const Formula* hi = newFormula( auxVar );
                                    hi->setDifficulty( currentSubformula->difficulty() );
                                    iter.first->second = new pair<const Formula*,const Formula*>( hi, newNegation( hi ) );
                                }
                                for( const Formula* subsubformula : currentSubformula->subformulas() )
                                    subformulasToTransformTmp.push_back( newFormula( OR, iter.first->second->second, subsubformula ) );
                                subsubformulas.insert( iter.first->second->first );
                                break;
                            }
                            case CONSTRAINT: // p~0 -> p~0
                            {
                                #ifdef REMOVE_LESS_EQUAL_IN_CNF_TRANSFORMATION
                                if( currentSubformula->constraint().relation() == Relation::LEQ )
                                {
                                    subsubformulas.insert( newFormula( newConstraint( currentSubformula->constraint().lhs(), Relation::LESS ) ) );
                                    subsubformulas.insert( newFormula( newConstraint( currentSubformula->constraint().lhs(), Relation::EQ ) ) );
                                }
                                else
                                {
                                #endif
                                #ifdef REMOVE_UNEQUAL_IN_CNF_TRANSFORMATION
                                if( currentSubformula->constraint().relation() == Relation::NEQ )
                                {
                                    subsubformulas.insert( newFormula( newConstraint( currentSubformula->constraint().lhs(), Relation::LESS ) ) );
                                    subsubformulas.insert( newFormula( newConstraint( -currentSubformula->constraint().lhs(), Relation::LESS ) ) );
                                }
                                else
                                {
                                #endif
                                subsubformulas.insert( currentSubformula );
                                #ifdef REMOVE_UNEQUAL_IN_CNF_TRANSFORMATION
                                }
                                #endif
                                #ifdef REMOVE_LESS_EQUAL_IN_CNF_TRANSFORMATION
                                }
                                #endif
                                break;
                            }
                            case IFF: // (iff phi_1 .. phi_n) -> (and phi_1 .. phi_n) and (and (not phi_1) .. (not phi_n)) are added to the queue
                            {
                                PointerSet<Formula> subformulasA;
                                PointerSet<Formula> subformulasB;
                                for( auto subformula : currentSubformula->subformulas() )
                                {
                                    subformulasA.insert( subformula );
                                    subformulasB.insert( newNegation( subformula ) );
                                }
                                phis.push_back( newFormula( AND, move( subformulasA ) ) );
                                phis.push_back( newFormula( AND, move( subformulasB ) ) );
                                break;
                            }
                            case XOR: // (xor lhs rhs) -> (and lhs (not rhs)) and (and (not lhs) rhs) are added to the queue
                            {
                                // Get lhs and rhs.
                                const Formula* lhs = currentSubformula->connectPrecedingSubformulas();
                                const Formula* rhs = currentSubformula->back();
                                // add (and lhs (not rhs)) to the queue
                                phis.push_back( newFormula( AND, lhs, newNegation( rhs )) );
                                // add (and (not lhs) rhs) to the queue
                                phis.push_back( newFormula( AND, newNegation( lhs ), rhs ) );
                                break;
                            }
                            default:
                            {
                                assert( false );
                                cerr << "Unexpected type of formula!" << endl;
                            }
                        }
                    }
                    if( !currentFormulaValid )
                    {
                        subformulasToTransform.insert( subformulasToTransform.end(), subformulasToTransformTmp.begin(), subformulasToTransformTmp.end() );
                        if( subsubformulas.empty() ) // Empty clause = false, which, added to a conjunction, leads to false.
                        {
                            goto ReturnFalse;
                        }
                        else if( subsubformulas.size() == 1 )
                        {
                            subformulas.insert( *subsubformulas.begin() );
                        }
                        else
                        {
                            subformulas.insert( newFormula( OR, move( subsubformulas ) ) );
                        }
                    }
                    break;
                }
                default:
                {
                    assert( false );
                    cerr << "Unexpected type of formula!" << endl;
                }
            }
        }
        if( subformulas.empty() )
            return trueFormula();
        else if( subformulas.size() == 1 )
            return *subformulas.begin();
        else
            return newFormula( AND, move( subformulas ) );
        ReturnFalse:
            while( !tseitinVars.empty() )
            {
                auto toDel = tseitinVars.begin()->second;
                tseitinVars.erase( tseitinVars.begin() );
                delete toDel;
            }
            return falseFormula();
    }
}    // namespace smtrat

