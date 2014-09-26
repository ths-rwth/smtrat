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


#include "Formula.h"
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
    
    Formula::Formula( carl::Variable::Arg _boolean ):
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

    Formula::Formula(const Type _type, const std::vector<carl::Variable>&& _vars, const Formula* _term):
        mDeducted( false ),
        ///@todo Construct reasonable hash
        mHash( _term->getHash() ),
        mId( 0 ),
        mActivity( 0 ),
        mDifficulty( 0 ),
        mType( _type ),
        mProperties()
    {
        assert(_type == EXISTS || _type == FORALL);
        mpQuantifierContent = new QuantifierContent(std::move(_vars), _term);
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
            case EXISTS:
            case FORALL:
                quantifiedFormula().collectVariables(_vars, _type, _ofThisType);
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
                    return premise() == _formula.premise() && conclusion() == _formula.conclusion();
                case ITE:
                    return condition() == _formula.condition() && firstCase() == _formula.firstCase() && secondCase() == _formula.secondCase();
                case Type::EXISTS:
                    return (*this->mpQuantifierContent == *_formula.mpQuantifierContent);
                case Type::FORALL:
                    return (*this->mpQuantifierContent == *_formula.mpQuantifierContent);
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
            case EXISTS:
            {
                ///@todo do something here
                return 2;
                break;
            }
            case FORALL:
            {
                ///@todo do something here
                return 2;
                break;
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
            case EXISTS:
            {
                ///@todo do something here
                break;
            }
            case FORALL:
            {
                ///@todo do something here
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
        else if (mType == EXISTS)
        {
            string result = _init + "(exists ";
            for (auto v: this->mpQuantifierContent->mVariables) {
                result += constraintPool().getVariableName(v, _friendlyNames) + " ";
            }
            result += this->mpQuantifierContent->mpFormula->toString(_withActivity, _resolveUnequal, _init, _oneline, _infix, _friendlyNames);
            result += ")";
            return result;
        }
        else if (mType == FORALL)
        {
            string result = _init + "(forall ";
            for (auto v: this->mpQuantifierContent->mVariables) {
                result += constraintPool().getVariableName(v, _friendlyNames) + " ";
            }
            result += this->mpQuantifierContent->mpFormula->toString(_withActivity, _resolveUnequal, _init, _oneline, _infix, _friendlyNames);
            result += ")";
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
                const Constraint* constraint = mpSubformula->pConstraint();
                if( _keepConstraint )
                    return this;
                else
                {
                    switch( constraint->relation() )
                    {
                        case Relation::EQ:
                        {
                            return newFormula( newConstraint( constraint->lhs(), Relation::NEQ ) );
                        }
                        case Relation::LEQ:
                        {
                            return newFormula( newConstraint( -constraint->lhs(), Relation::LESS ) );
                        }
                        case Relation::LESS:
                        {
                            return newFormula( newConstraint( -constraint->lhs(), Relation::LEQ ) );
                        }
                        case Relation::GEQ:
                        {
                            return newFormula( newConstraint( constraint->lhs(), Relation::LESS ) );
                        }
                        case Relation::GREATER:
                        {
                            return newFormula( newConstraint( constraint->lhs(), Relation::LEQ ) );
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
            case EXISTS: // (not (exists (vars) phi)) -> (forall (vars) (not phi))
                break;
                newType = FORALL;
            case FORALL: // (not (forall (vars) phi)) -> (exists (vars) (not phi))
                break;
                newType = EXISTS;
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

    const Formula* Formula::toQF(QuantifiedVariables& variables, unsigned level, bool negated) const
    {
        const Formula* res;
        switch (this->mType) {
            case Type::AND:
            case Type::IFF:
            case Type::OR:
            case Type::XOR:
            {
                if (!negated) {
                    PointerSet<Formula> subs;
                    for (auto sub: *this->mpSubformulas) {
                        subs.insert(sub->toQF(variables, level, false));
                    }
                    res = newFormula(this->mType, std::move(subs));
                } else if (this->mType == Type::AND || this->mType == Type::OR) {
                    PointerSet<Formula> subs;
                    for (auto sub: *this->mpSubformulas) {
                        subs.insert(sub->toQF(variables, level, true));
                    }
                    if (this->mType == Type::AND) res = newFormula(Type::OR, std::move(subs));
                    else res = newFormula(Type::AND, std::move(subs));
                } else if (this->mType == Type::IFF) {
                    PointerSet<Formula> sub1;
                    PointerSet<Formula> sub2;
                    for (auto sub: *this->mpSubformulas) {
                        sub1.insert(sub->toQF(variables, level, true));
                        sub2.insert(sub->toQF(variables, level, false));
                    }
                    res = newFormula(Type::AND, newFormula(Type::OR, std::move(sub1)), newFormula(Type::OR, std::move(sub2)));
                } else if (this->mType == Type::XOR) {
                    auto lhs = this->back()->toQF(variables, level, false);
                    auto rhs = this->connectPrecedingSubformulas()->toQF(variables, level, true);
                    res = newFormula(Type::IFF, lhs, rhs);
                } else assert(false);
                break;
            }
            case Type::BOOL:
            case Type::CONSTRAINT:
            case Type::FFALSE:
            case Type::TTRUE:
            {
                if (negated) res = newNegation(this);
                else res = this;
                break;
            }
            case Type::EXISTS:
            case Type::FORALL:
            {
                unsigned cur = 0;
                if ((level % 2 == (mType == Type::EXISTS ? (unsigned)0 : (unsigned)1)) xor negated) cur = level;
                else cur = level+1;
                Variables vars(this->quantifiedVariables().begin(), this->quantifiedVariables().end());
                const Formula* f = this->pQuantifiedFormula();
                for (auto it = vars.begin(); it != vars.end();) {
                    if (it->getType() == carl::VariableType::VT_BOOL) {
                        // Just leave boolean variables at the base level up to the SAT solver.
                        if (cur > 0) {
                            f = newFormula(
                                (mType == Type::EXISTS ? Type::OR : Type::AND),
                                f->substitute({{*it, trueFormula()}}),
                                f->substitute({{*it, falseFormula()}})
                            );
                        }
                        it = vars.erase(it);
                    }
                    else it++;
                }
                if (vars.size() > 0) {
                    while (variables.size() <= cur) variables.emplace_back();
                    variables[cur].insert(vars.begin(), vars.end());
                }
                res = f->toQF(variables, cur, negated);
                break;
            }
            case Type::IMPLIES:
                if (negated) res = newFormula(Type::AND, pPremise()->toQF(variables, level, false), pConclusion()->toQF(variables, level, true));
                else res = newImplication(pPremise()->toQF(variables, level, false), pConclusion()->toQF(variables, level, false));
                break;
            case Type::ITE:
                res = newIte(pCondition()->toQF(variables, level, negated), pFirstCase()->toQF(variables, level, negated), pSecondCase()->toQF(variables, level, negated));
                break;
            case Type::NOT:
                res = this->pSubformula()->toQF(variables, level, !negated);
                break;
        }
        return res;
    }

    const Formula* Formula::toCNF( bool _keepConstraints, bool _simplifyConstraintCombinations ) const
    {
        if( !_simplifyConstraintCombinations && propertyHolds( PROP_IS_IN_CNF ) )
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
        PointerSet<Formula> resultSubformulas;
        ConstraintBounds constraintBoundsAnd;
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
//            for( auto f : resultSubformulas )
//                cout << "   " << *f << endl;
//            cout << endl;
            subformulasToTransform.pop_back();
            switch( currentFormula->getType() )
            {
                case BOOL:
                {
                    resultSubformulas.insert( currentFormula );
                    break;
                }
                case CONSTRAINT:
                {   
                    if( _simplifyConstraintCombinations )
                    {
                        if( addConstraintBound( constraintBoundsAnd, currentFormula, true ) )
                        {
                            goto ReturnFalse;
                        }
                    }
                    else
                        resultSubformulas.insert( currentFormula );
                    break;
                }
                case TTRUE: // Remove it.
                    break;
                case FFALSE: // Return false.
                    goto ReturnFalse;
                case NOT: // Try to resolve this negation.
                {
                    const Formula* resolvedFormula = currentFormula->resolveNegation( _keepConstraints );
                    if( resolvedFormula->propertyHolds( PROP_IS_A_LITERAL ) ) // It is a literal.
                    {
                        if( resolvedFormula->getType() == CONSTRAINT || (resolvedFormula->getType() == NOT && resolvedFormula->subformula().getType() == CONSTRAINT) )
                        {
                            if( _simplifyConstraintCombinations )
                            {
                                if( addConstraintBound( constraintBoundsAnd, resolvedFormula, true ) )
                                {
                                    goto ReturnFalse;
                                }
                            }
                            else
                            {
                                resultSubformulas.insert( resolvedFormula );
                            }
                        }
                        else
                        {
                            resultSubformulas.insert( resolvedFormula );
                        }
                    }
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
                case ITE: // (ite cond then else)  ->  auxBool, where (or (not cond) then) and (or cond else) are added to the queue
                {
                    // Add: (or (not cond) then)
                    subformulasToTransform.push_back( newFormula( OR, newNegation( currentFormula->pCondition() ), currentFormula->pFirstCase() ) );
                    // Add: (or cond else)
                    subformulasToTransform.push_back( newFormula( OR, currentFormula->pCondition(), currentFormula->pSecondCase() ) );
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
                    ConstraintBounds constraintBoundsOr;
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
                            case ITE: // (ite cond then else)  ->  (and (or (not cond) then) (or cond else))
                            {   
                                PointerSet<Formula> tmpSubformulas;
                                // Add: (or (not cond) then)
                                tmpSubformulas.insert( newFormula( OR, newNegation( currentSubformula->pCondition() ), currentSubformula->pFirstCase() ) );
                                // Add: (or cond else)
                                tmpSubformulas.insert( newFormula( OR, currentSubformula->pCondition(), currentSubformula->pSecondCase() ) );
                                phis.push_back( newFormula( AND, tmpSubformulas ) );
                                break;
                            }
                            case NOT: // resolve the negation
                            {
                                const Formula* resolvedFormula = currentSubformula->resolveNegation( _keepConstraints );
                                if( resolvedFormula->propertyHolds( PROP_IS_A_LITERAL ) ) // It is a literal.
                                {
                                    if( resolvedFormula->getType() == CONSTRAINT || (resolvedFormula->getType() == NOT && resolvedFormula->subformula().getType() == CONSTRAINT) )
                                    {
                                        if( _simplifyConstraintCombinations )
                                        {
                                            if( addConstraintBound( constraintBoundsOr, resolvedFormula, false ) )
                                            {
                                                currentFormulaValid = true;
                                                break;
                                            }
                                        }
                                        else
                                        {
                                            subsubformulas.insert( resolvedFormula );
                                        }
                                    }
                                    else
                                    {
                                        subsubformulas.insert( resolvedFormula );
                                    }
                                }
                                else
                                    phis.push_back( resolvedFormula );
                                break;
                            }
                            case AND: // (and phi_i1 .. phi_ik) -> h_i, where (or (not h_i) phi_i1) .. (or (not h_i) phi_ik) 
                                      //                                and (or h_i (not phi_i1) .. (not phi_ik))  is added to the queue
                            {
                                bool conjunctionIsFalse = false;
                                ConstraintBounds constraintBoundsOrAnd;
                                PointerSet<Formula> tmpSubSubformulas;
                                for( const Formula* subsubformula : currentSubformula->subformulas() )
                                {
                                    if( subsubformula->getType() == CONSTRAINT || (subsubformula->getType() == NOT && subsubformula->subformula().getType() == CONSTRAINT ) )
                                    {
                                        if( _simplifyConstraintCombinations )
                                        {
                                            if( addConstraintBound( constraintBoundsOrAnd, subsubformula, true ) )
                                            {
                                                conjunctionIsFalse = true;
                                                break;
                                            }
                                        }
                                        else
                                        {
                                            tmpSubSubformulas.insert( subsubformula );
                                        }
                                    }
                                    else
                                    {
                                        tmpSubSubformulas.insert( subsubformula );
                                    }
                                }
                                if( conjunctionIsFalse )
                                    break;
                                if( _simplifyConstraintCombinations && swapConstraintBounds( constraintBoundsOrAnd, tmpSubSubformulas, true ) )
                                    break;
                                auto iter = tseitinVars.insert( pair<const Formula*,pair<const Formula*,const Formula*>*>( currentSubformula, NULL ) );
                                if( iter.second )
                                {
                                    carl::Variable auxVar = newAuxiliaryBooleanVariable();
                                    const Formula* hi = newVariableFormula( auxVar );
                                    hi->setDifficulty( currentSubformula->difficulty() );
                                    iter.first->second = new pair<const Formula*,const Formula*>( hi, newNegation( hi ) );
                                }
                                for( const Formula* subsubformula : tmpSubSubformulas )
                                    subformulasToTransformTmp.push_back( newFormula( OR, iter.first->second->second, subsubformula ) );
                                PointerSet<Formula> tmpSubformulas;
                                tmpSubformulas.insert( iter.first->second->first );
                                for( const Formula* subsubformula : tmpSubSubformulas )
                                    tmpSubformulas.insert( newNegation( subsubformula ) );
                                subformulasToTransformTmp.push_back( newFormula( OR, tmpSubformulas ) );
                                subsubformulas.insert( iter.first->second->first );
                                break;
                            }
                            case CONSTRAINT: // p~0 -> p~0
                            {
                                if( _simplifyConstraintCombinations )
                                {
                                    if( addConstraintBound( constraintBoundsOr, currentSubformula, false ) )
                                    {
                                        currentFormulaValid = true;
                                        break;
                                    }
                                }
                                else
                                {
                                    subsubformulas.insert( currentSubformula );
                                }
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
                            case EXISTS:
                            {
                                assert(false);
                                std::cerr << "Formula must be quantifier-free!" << std::endl;
                                break;
                            }
                            case FORALL:
                            {
                                assert(false);
                                std::cerr << "Formula must be quantifier-free!" << std::endl;
                                break;
                            }
                            default:
                            {
                                assert( false );
                                cerr << "Unexpected type of formula!" << endl;
                            }
                        }
                    }
                    if( !currentFormulaValid && (!_simplifyConstraintCombinations || !swapConstraintBounds( constraintBoundsOr, subsubformulas, false )) )
                    {
                        subformulasToTransform.insert( subformulasToTransform.end(), subformulasToTransformTmp.begin(), subformulasToTransformTmp.end() );
                        if( subsubformulas.empty() ) // Empty clause = false, which, added to a conjunction, leads to false.
                        {
                            goto ReturnFalse;
                        }
                        else if( subsubformulas.size() == 1 )
                        {
                            resultSubformulas.insert( *subsubformulas.begin() );
                        }
                        else
                        {
                            resultSubformulas.insert( newFormula( OR, move( subsubformulas ) ) );
                        }
                    }
                    break;
                }
                case EXISTS:
                {
                    assert(false);
                    std::cerr << "Formula must be quantifier-free!" << std::endl;
                    break;
                }
                case FORALL:
                {
                    assert(false);
                    std::cerr << "Formula must be quantifier-free!" << std::endl;
                    break;
                }
                default:
                {
                    assert( false );
                    cerr << "Unexpected type of formula!" << endl;
                }
            }
        }
        if( _simplifyConstraintCombinations && swapConstraintBounds( constraintBoundsAnd, resultSubformulas, true ) )
            goto ReturnFalse;
        if( resultSubformulas.empty() )
            return trueFormula();
        else if( resultSubformulas.size() == 1 )
            return *resultSubformulas.begin();
        else
            return newFormula( AND, move( resultSubformulas ) );
        ReturnFalse:
            while( !tseitinVars.empty() ) // TODO: why only here?
            {
                auto toDel = tseitinVars.begin()->second;
                tseitinVars.erase( tseitinVars.begin() );
                delete toDel;
            }
            return falseFormula();
    }
            
    const Formula* Formula::substitute( const map<carl::Variable, const Formula*>& _booleanSubstitutions, const map<carl::Variable, Polynomial>& _arithmeticSubstitutions ) const
    {
        switch( mType )
        {
            case TTRUE:
            {
                return this;
            }
            case FFALSE:
            {
                return this;
            }
            case BOOL:
            {
                auto iter = _booleanSubstitutions.find( mBoolean );
                if( iter != _booleanSubstitutions.end() )
                {
                    return iter->second;
                }
                return this;
            }
            case CONSTRAINT:
            {
                Polynomial lhsSubstituted = mpConstraint->lhs().substitute( _arithmeticSubstitutions );
                return newFormula( newConstraint( lhsSubstituted, mpConstraint->relation() ) );
            }
            case NOT:
            {
                return newNegation( mpSubformula->substitute( _booleanSubstitutions, _arithmeticSubstitutions ) );
            }
            case IMPLIES:
            {
                const Formula* premiseSubstituted = premise().substitute( _booleanSubstitutions, _arithmeticSubstitutions );
                const Formula* conclusionSubstituted = conclusion().substitute( _booleanSubstitutions, _arithmeticSubstitutions );
                return newImplication( premiseSubstituted, conclusionSubstituted );
            }
            case ITE:
            {
                const Formula* conditionSubstituted = condition().substitute( _booleanSubstitutions, _arithmeticSubstitutions );
                const Formula* thenSubstituted = firstCase().substitute( _booleanSubstitutions, _arithmeticSubstitutions );
                const Formula* elseSubstituted = secondCase().substitute( _booleanSubstitutions, _arithmeticSubstitutions );
                return newIte( conditionSubstituted, thenSubstituted, elseSubstituted );
            }
            case Type::EXISTS:
            case Type::FORALL:
            {
                return newQuantifier(mType, quantifiedVariables(), quantifiedFormula().substitute(_booleanSubstitutions, _arithmeticSubstitutions));
            }
            default:
            {
                assert( isNary() );
                PointerSet<Formula> subformulasSubstituted;
                for( const Formula* subformula : subformulas() )
                    subformulasSubstituted.insert( subformula->substitute( _booleanSubstitutions, _arithmeticSubstitutions ) );
                return newFormula( mType, subformulasSubstituted );
            }
        }
    }
    
//    #define CONSTRAINT_BOUND_DEBUG

    bool Formula::addConstraintBound( ConstraintBounds& _constraintBounds, const Formula* _constraint, bool _inConjunction )
    {
        #ifdef CONSTRAINT_BOUND_DEBUG
        cout << "add from a " << (_inConjunction ? "conjunction" : "disjunction") << " to " << &_constraintBounds << ":   " << *_constraint << endl;
        #endif
        bool negated = _constraint->getType() == NOT;
        assert( _constraint->getType() == CONSTRAINT || (negated && _constraint->subformula().getType() == CONSTRAINT ) );
        const Constraint& constraint = negated ? _constraint->subformula().constraint() : _constraint->constraint();
        assert( constraint.isConsistent() == 2 );
        Rational boundValue;
        Relation relation = negated ? Constraint::invertRelation( constraint.relation() ) : constraint.relation();
        const Polynomial& lhs = constraint.lhs();
        Polynomial* poly = NULL;
        if( lhs.nrTerms() == 1 || ( lhs.nrTerms() == 2 && lhs.hasConstantTerm() ) )
        {
            auto term = lhs.begin();
            for( ; term != lhs.end(); ++term )
                if( !(*term)->isConstant() ) break;
            poly = new Polynomial( (*term)->monomial()->begin()->first );
            Rational primCoeff( (*term)->coeff() );
            if( primCoeff < Rational( 0 ) )
                relation = Constraint::turnAroundRelation( relation );
            boundValue = Rational( -constraint.constantPart() )/primCoeff;
        }
        else
        {
            if( lhs.lterm()->coeff() < Rational( 0 ) )
            {
                boundValue = constraint.constantPart();
                relation = Constraint::turnAroundRelation( relation );
                poly = new Polynomial( -lhs + boundValue );
            }
            else
            {
                boundValue = -constraint.constantPart();
                poly = new Polynomial( lhs + boundValue );
            }
            Rational cf( poly->coprimeFactor() );
            assert( cf > 0 );
            boundValue *= cf;
            (*poly) *= cf;
        }
        #ifdef CONSTRAINT_BOUND_DEBUG
        cout << "try to add the bound  " << Constraint::relationToString( relation ) << boundValue << "  for the polynomial  " << *poly << endl; 
        #endif
        auto resA = _constraintBounds.insert( make_pair( poly, std::move( map<Rational, pair<Relation, const Formula*>>() ) ) );
        if( !resA.second )
        {
            delete poly;
        }
        auto resB = resA.first->second.insert( make_pair( boundValue, make_pair( relation, _constraint ) ) );
        if( resB.second || resB.first->second.first == relation )
            return false;
        switch( relation )
        {
            case Relation::EQ:
                if( _inConjunction )
                {
                    if( resB.first->second.first == Relation::LEQ || resB.first->second.first == Relation::GEQ )
                    {
                        resB.first->second.first = Relation::EQ;
                        resB.first->second.second = _constraint;
                        return false;
                    }
                    else
                        return true;
                }
                else
                {
                    switch( resB.first->second.first )
                    {
                        case Relation::LEQ:
                            return false;
                        case Relation::GEQ:
                            return false;
                        case Relation::LESS:
                            resB.first->second.first = Relation::LEQ;
                            resB.first->second.second = _constraint;
                            return false;
                        case Relation::GREATER:
                            resB.first->second.first = Relation::GEQ;
                            resB.first->second.second = _constraint;
                            return false;
                        default:
                            assert( resB.first->second.first == Relation::NEQ );
                            return true;
                    }
                }
            case Relation::LEQ:
                if( _inConjunction )
                {
                    switch( resB.first->second.first )
                    {
                        case Relation::EQ:
                            return false;
                        case Relation::GEQ:
                            resB.first->second.first = Relation::EQ;
                            resB.first->second.second = _constraint;
                            return false;
                        case Relation::LESS:
                            return false;
                        case Relation::GREATER:
                            return true;
                        default:
                            assert( resB.first->second.first == Relation::NEQ );
                            resB.first->second.first = Relation::LESS;
                            resB.first->second.second = newFormula( newConstraint( lhs, Relation::LESS ) );
                            return false;
                    }
                }
                else
                {
                    switch( resB.first->second.first )
                    {
                        case Relation::EQ:
                            resB.first->second.first = Relation::LEQ;
                            resB.first->second.second = _constraint;
                            return false;
                        case Relation::GEQ:
                            return true;
                        case Relation::LESS:
                            resB.first->second.first = Relation::LEQ;
                            resB.first->second.second = _constraint;
                            return false;
                        case Relation::GREATER:
                            return true;
                        default:
                            assert( resB.first->second.first == Relation::NEQ );
                            return true;
                    }
                }
            case Relation::GEQ:
                if( _inConjunction )
                {
                    switch( resB.first->second.first )
                    {
                        case Relation::EQ:
                            return false;
                        case Relation::LEQ:
                            resB.first->second.first = Relation::EQ;
                            resB.first->second.second = _constraint;
                            return false;
                        case Relation::LESS:
                            return true;
                        case Relation::GREATER:
                            return false;
                        default:
                            assert( resB.first->second.first == Relation::NEQ );
                            resB.first->second.first = Relation::GREATER;
                            resB.first->second.second = newFormula( newConstraint( lhs, Relation::GREATER ) );
                            return false;
                    }
                }
                else
                {
                    switch( resB.first->second.first )
                    {
                        case Relation::EQ:
                            resB.first->second.first = Relation::GEQ;
                            resB.first->second.second = _constraint;
                            return false;
                        case Relation::LEQ:
                            return true;
                        case Relation::LESS:
                            return true;
                        case Relation::GREATER:
                            resB.first->second.first = Relation::GEQ;
                            resB.first->second.second = _constraint;
                            return true;
                        default:
                            assert( resB.first->second.first == Relation::NEQ );
                            return true;
                    }
                }
            case Relation::LESS:
                if( _inConjunction )
                {
                    switch( resB.first->second.first )
                    {
                        case Relation::EQ:
                            return true;
                        case Relation::LEQ:
                            resB.first->second.first = Relation::LESS;
                            resB.first->second.second = _constraint;
                            return false;
                        case Relation::GEQ:
                            return true;
                        case Relation::GREATER:
                            return true;
                        default:
                            assert( resB.first->second.first == Relation::NEQ );
                            resB.first->second.first = Relation::LESS;
                            resB.first->second.second = _constraint;
                            return false;
                    }
                }
                else
                {
                    switch( resB.first->second.first )
                    {
                        case Relation::EQ:
                            resB.first->second.first = Relation::LEQ;
                            resB.first->second.second = _constraint;
                            return false;
                        case Relation::LEQ:
                            return false;
                        case Relation::GEQ:
                            return true;
                        case Relation::GREATER:
                            resB.first->second.first = Relation::NEQ;
                            resB.first->second.second = newFormula( newConstraint( lhs, Relation::NEQ ) );
                            return false;
                        default:
                            assert( resB.first->second.first == Relation::NEQ );
                            return false;
                    }
                }
            case Relation::GREATER:
                if( _inConjunction )
                {
                    switch( resB.first->second.first )
                    {
                        case Relation::EQ:
                            return true;
                        case Relation::LEQ:
                            return true;
                        case Relation::GEQ:
                            resB.first->second.first = Relation::GREATER;
                            resB.first->second.second = _constraint;
                            return false;
                        case Relation::LESS:
                            return true;
                        default:
                            assert( resB.first->second.first == Relation::NEQ );
                            resB.first->second.first = Relation::GREATER;
                            resB.first->second.second = _constraint;
                            return false;
                    }
                }
                else
                {
                    switch( resB.first->second.first )
                    {
                        case Relation::EQ:
                            resB.first->second.first = Relation::GEQ;
                            resB.first->second.second = _constraint;
                            return false;
                        case Relation::LEQ:
                            return true;
                        case Relation::GEQ:
                            return false;
                        case Relation::LESS:
                            resB.first->second.first = Relation::NEQ;
                            resB.first->second.second = newFormula( newConstraint( lhs, Relation::NEQ ) );
                            return false;
                        default:
                            assert( resB.first->second.first == Relation::NEQ );
                            return false;
                    }
                }
            default:
                assert( relation == Relation::NEQ );
                if( _inConjunction )
                {
                    switch( resB.first->second.first )
                    {
                        case Relation::EQ:
                            return true;
                        case Relation::LEQ:
                            resB.first->second.first = Relation::LESS;
                            resB.first->second.second = newFormula( newConstraint( lhs, Relation::LESS ) );
                            return false;
                        case Relation::GEQ:
                            resB.first->second.first = Relation::GREATER;
                            resB.first->second.second = newFormula( newConstraint( lhs, Relation::GREATER ) );
                            return false;
                        case Relation::LESS:
                            resB.first->second.first = Relation::LESS;
                            resB.first->second.second = _constraint;
                            return false;
                        default:
                            assert( resB.first->second.first == Relation::GREATER );
                            resB.first->second.first = Relation::GREATER;
                            resB.first->second.second = _constraint;
                            return false;
                    }
                }
                else
                {
                    switch( resB.first->second.first )
                    {
                        case Relation::EQ:
                            return true;
                        case Relation::LEQ:
                            return true;
                        case Relation::GEQ:
                            return true;
                        case Relation::LESS:
                            return false;
                        default:
                            assert( resB.first->second.first == Relation::GREATER );
                            return false;
                    }
                }
        }
    }

    bool Formula::swapConstraintBounds( ConstraintBounds& _constraintBounds, PointerSet<Formula>& _intoFormulas, bool _inConjunction )
    {
        #ifdef CONSTRAINT_BOUND_DEBUG
        cout << "swap from " << &_constraintBounds << " to a " << (_inConjunction ? "conjunction" : "disjunction") << endl;
        #endif
        while( !_constraintBounds.empty() )
        {
            #ifdef CONSTRAINT_BOUND_DEBUG
            cout << "for the bounds of  " << *_constraintBounds.begin()->first << endl;
            #endif
            const map<Rational, pair<Relation, const Formula*>>& bounds = _constraintBounds.begin()->second;
            assert( !bounds.empty() );
            if( bounds.size() == 1 )
            {
                _intoFormulas.insert( bounds.begin()->second.second );
                #ifdef CONSTRAINT_BOUND_DEBUG
                cout << "   just add the only bound" << endl;
                #endif
            }
            else
            {
                auto mostSignificantLowerBound = bounds.end();
                auto mostSignificantUpperBound = bounds.end();
                auto moreSignificantCase = bounds.end();
                PointerSet<Formula> lessSignificantCases;
                auto iter = bounds.begin();
                for( ; iter != bounds.end(); ++iter )
                {
                    #ifdef CONSTRAINT_BOUND_DEBUG
                    cout << "   bound is  " << Constraint::relationToString( iter->second.first ) << iter->first << endl;
                    #endif
                    if( (_inConjunction && iter->second.first == Relation::NEQ)
                        || (!_inConjunction && iter->second.first == Relation::EQ) )
                    {
                        if( moreSignificantCase == bounds.end() )
                        {
                            if( (_inConjunction && mostSignificantUpperBound == bounds.end())
                                || (!_inConjunction && mostSignificantLowerBound == bounds.end()) )
                            {
                                if( (_inConjunction && mostSignificantLowerBound != bounds.end())
                                    || (!_inConjunction && mostSignificantUpperBound != bounds.end()) )
                                {
                                    #ifdef CONSTRAINT_BOUND_DEBUG
                                    cout << "      case: " << __LINE__ << endl;
                                    #endif
                                    _intoFormulas.insert( iter->second.second );
                                }
                                else
                                {
                                    #ifdef CONSTRAINT_BOUND_DEBUG
                                    cout << "      case: " << __LINE__ << endl;
                                    #endif
                                    lessSignificantCases.insert( iter->second.second );
                                }
                            }
                        }
                    }
                    else if( (_inConjunction && (iter->second.first == Relation::GEQ || iter->second.first == Relation::GREATER)) // found a lower bound
                             || (!_inConjunction && (iter->second.first == Relation::LEQ || iter->second.first == Relation::LESS)) ) // found an upper bound
                    {
                        if( (_inConjunction && mostSignificantUpperBound != bounds.end()) // found already an upper bound -> conjunction is invalid!
                            || (!_inConjunction && mostSignificantLowerBound != bounds.end()) // found already a lower bound -> disjunction is valid!
                            || moreSignificantCase != bounds.end() )
                        {
                            #ifdef CONSTRAINT_BOUND_DEBUG
                            cout << "      case: " << __LINE__ << endl;
                            #endif
                            break;
                        }
                        else
                        {
                            #ifdef CONSTRAINT_BOUND_DEBUG
                            cout << "      case: " << __LINE__ << endl;
                            #endif
                            if( _inConjunction ) // update the strongest upper bound
                                mostSignificantLowerBound = iter;
                            else // update the weakest upper bound
                                mostSignificantUpperBound = iter;
                            lessSignificantCases.clear();
                        }
                    }
                    else if( (_inConjunction && iter->second.first == Relation::EQ)
                            || (!_inConjunction && iter->second.first == Relation::NEQ) )
                    {
                        // _inConjunction == true: found already another equality or an upper bound -> conjunction is invalid!
                        // _inConjunction == false: found already another bound with != as relation or a lower bound -> disjunction is valid!
                        if( moreSignificantCase != bounds.end() || mostSignificantUpperBound != bounds.end() )
                        {
                            #ifdef CONSTRAINT_BOUND_DEBUG
                            cout << "      case: " << __LINE__ << endl;
                            #endif
                            break;
                        }
                        // _inConjunction == true: found first equality
                        // _inConjunction == false: found first bound with !=
                        else 
                        {
                            #ifdef CONSTRAINT_BOUND_DEBUG
                            cout << "      case: " << __LINE__ << endl;
                            #endif
                            moreSignificantCase = iter;
                        }
                    }
                    // _inConjunction == true: found an upper bound
                    // _inConjunction == false: found a lower bound
                    else
                    {
                        #ifdef CONSTRAINT_BOUND_DEBUG
                        cout << "      case: " << __LINE__ << endl;
                        #endif
                        assert( !_inConjunction || iter->second.first == Relation::LEQ || iter->second.first == Relation::LESS );
                        assert( _inConjunction || iter->second.first == Relation::GEQ || iter->second.first == Relation::GREATER );
                        if( _inConjunction && mostSignificantUpperBound == bounds.end() ) // first upper bound found = strongest upper bound
                        {
                            #ifdef CONSTRAINT_BOUND_DEBUG
                            cout << "      case: " << __LINE__ << endl;
                            #endif
                            mostSignificantUpperBound = iter;
                        }
                        else if( !_inConjunction && mostSignificantLowerBound == bounds.end() ) // first lower bound found = weakest lower bound
                        {
                            #ifdef CONSTRAINT_BOUND_DEBUG
                            cout << "      case: " << __LINE__ << endl;
                            #endif
                            mostSignificantLowerBound = iter;
                        }
                    }
                }
                if( iter != bounds.end() )
                    break;
                if( moreSignificantCase != bounds.end() )
                {
                    _intoFormulas.insert( moreSignificantCase->second.second );
                }
                else
                {
                    #ifdef CONSTRAINT_BOUND_DEBUG
                    if( !(_inConjunction || mostSignificantUpperBound == bounds.end() || mostSignificantLowerBound == bounds.end() 
                            || mostSignificantUpperBound->first > mostSignificantLowerBound->first) 
                        || !( !_inConjunction || mostSignificantUpperBound == bounds.end() || mostSignificantLowerBound == bounds.end() 
                             || mostSignificantLowerBound->first > mostSignificantUpperBound->first ) )
                    {
                        cout << "mostSignificantUpperBound:   " << mostSignificantUpperBound->first << "  [" << *mostSignificantUpperBound->second.second << "]" << endl;
                        cout << "mostSignificantLowerBound:   " << mostSignificantLowerBound->first << "  [" << *mostSignificantLowerBound->second.second << "]" << endl;
                    }
                    #endif
                    assert( !_inConjunction || mostSignificantUpperBound == bounds.end() || mostSignificantLowerBound == bounds.end() 
                            || mostSignificantUpperBound->first > mostSignificantLowerBound->first );
                    assert( _inConjunction || mostSignificantUpperBound == bounds.end() || mostSignificantLowerBound == bounds.end() 
                             || mostSignificantLowerBound->first > mostSignificantUpperBound->first );
                    if( mostSignificantUpperBound != bounds.end() )
                        _intoFormulas.insert( mostSignificantUpperBound->second.second );
                    if( mostSignificantLowerBound != bounds.end() )
                        _intoFormulas.insert( mostSignificantLowerBound->second.second );
                    _intoFormulas.insert( lessSignificantCases.begin(), lessSignificantCases.end() );
                }
            }
            const Polynomial* poly = _constraintBounds.begin()->first;
            _constraintBounds.erase( _constraintBounds.begin() );
            delete poly;
        }
        if( _constraintBounds.empty() )
        {
            #ifdef CONSTRAINT_BOUND_DEBUG
            cout << endl;
            #endif
            return false;
        }
        else
        {
            while( !_constraintBounds.empty() )
            {
                const Polynomial* poly = _constraintBounds.begin()->first;
                _constraintBounds.erase( _constraintBounds.begin() );
                delete poly;
            }
            #ifdef CONSTRAINT_BOUND_DEBUG
            cout << "is " << (_inConjunction ? "invalid" : "valid") << endl << endl;
            #endif
            return true;
        }
    }
}    // namespace smtrat

