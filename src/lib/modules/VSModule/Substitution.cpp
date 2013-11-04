/* SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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
 * Class to create a substitution object.
 * @author Florian Corzilius
 * @since 2010-05-11
 * @version 2013-10-23
 */

#include "Substitution.h"

using namespace std;

namespace vs
{
    Substitution::Substitution( const carl::Variable& _variable, const Type& _type, const Condition::Set& _oConditions, const smtrat::PointerSet<smtrat::Constraint>& _sideCondition ):
        mVariable( _variable ),
        mpTerm( new SqrtEx() ),
        mType( _type ),
        mpTermVariables( NULL ),
        mpOriginalConditions( new Condition::Set( _oConditions ) ),
        mSideCondition( _sideCondition )
    {}

    Substitution::Substitution( const carl::Variable& _variable, const SqrtEx& _term, const Type& _type, const Condition::Set& _oConditions, const smtrat::PointerSet<smtrat::Constraint>& _sideCondition ):
        mVariable( _variable ),
        mpTerm( new SqrtEx( _term ) ),
        mType( _type ),
        mpTermVariables( NULL ),
        mpOriginalConditions( new Condition::Set( _oConditions ) ),
        mSideCondition( _sideCondition )
    {}

    Substitution::Substitution( const Substitution& _sub ):
        mVariable( _sub.variable() ),
        mpTerm( new SqrtEx( _sub.term() ) ),
        mType( _sub.type() ),
        mpTermVariables( _sub.mpTermVariables == NULL ? NULL : new smtrat::Variables( *_sub.mpTermVariables ) ),
        mpOriginalConditions( new Condition::Set( _sub.originalConditions() ) ),
        mSideCondition( _sub.sideCondition() )
    {}

    Substitution::~Substitution()
    {
        if( mpTermVariables != NULL )
            delete mpTermVariables;
        delete mpTerm;
        delete mpOriginalConditions;
    }

    unsigned Substitution::valuate() const
    {
        if( type() == MINUS_INFINITY )
            return 9;
        else if( type() == NORMAL )
        {
            if( term().isConstant() )
                return 8;
            else
            {
                if( term().hasSqrt() )
                    return 4;
                else
                {
                    if( term().denominator().isConstant() )
                        return 6;
                    else
                        return 5;
                }
            }
        }
        else
        {
            if( term().isConstant() )
                return 7;
            else
            {
                if( term().hasSqrt() )
                    return 1;
                else
                {
                    if( term().denominator().isConstant() )
                        return 3;
                    else
                        return 2;
                }
            }
        }
    }

    bool Substitution::operator==( const Substitution& _substitution ) const
    {
        if( variable() == _substitution.variable() )
        {
            if( type() == _substitution.type() )
            {
                if( term() == _substitution.term() )
                {
                    if( sideCondition() == _substitution.sideCondition() )
                        return true;
                    else
                        return false;
                }
                else
                    return false;
            }
            else
                return false;
        }
        else
            return false;
    }

//    bool Substitution::operator<( const Substitution& _substitution ) const
//    {
//        if( variable() < _substitution.variable() )
//            return true;
//        else if( variable() == _substitution.variable() )
//        {
//            if( type() < _substitution.type() )
//                return true;
//            else if( type() == _substitution.type() )
//            {
//                if( term().constantPart() < _substitution.term().constantPart() )
//                    return true;
//                else if( term().constantPart() == _substitution.term().constantPart() )
//                {
//                    if( term().factor() < _substitution.term().factor() )
//                        return true;
//                    else if( term().factor() == _substitution.term().factor() )
//                    {
//                        if( term().radicand() < _substitution.term().radicand() )
//                            return true;
//                        else if( term().radicand() == _substitution.term().radicand() )
//                        {
//                            if( term().denominator() < _substitution.term().denominator() )
//                                return true;
//                            else if( sideCondition() < _substitution.sideCondition() )
//                                return true;
//                            else
//                                return false;
//                        }
//                        else
//                            return false;
//                    }
//                    else
//                        return false;
//                }
//                else
//                    return false;
//            }
//            else
//                return false;
//        }
//        else
//            return false;
//    }

    ostream& operator<<( ostream& _ostream, const Substitution& _substitution )
    {
        return (_ostream << _substitution.toString( true ));
    }

    string Substitution::toString( bool _friendlyNames ) const
    {
        string result = "[" + smtrat::Formula::constraintPool().getVariableName( mVariable, _friendlyNames ) + " -> ";
        switch( type() )
        {
            case NORMAL:
                return result + term().toString( true, _friendlyNames ) + "]";
            case PLUS_EPSILON:
                return result + term().toString( true, _friendlyNames ) + " + epsilon]";
            case MINUS_INFINITY:
                return result + "-infinity]";
            case INVALID:
                return result + "invalid]";
            default:
                assert( false );
                return result + "unknown]";
        }
    }

    void Substitution::print( bool _withOrigins, bool _withSideConditions, ostream& _out, const string& _init ) const
    {
        _out << _init << toString();
        if( _withOrigins )
        {
            _out << " from {";
            for( auto oCond = originalConditions().begin(); oCond != originalConditions().end(); ++oCond )
            {
                if( oCond != originalConditions().begin() )
                    _out << ", ";
                _out << (**oCond).constraint().toString( 0, true, true );
            }
            _out << "}";
        }
        if( _withSideConditions && !sideCondition().empty() )
        {
            _out << "  if  ";
            for( auto sCons = sideCondition().begin(); sCons != sideCondition().end(); ++sCons )
            {
                if( sCons != sideCondition().begin() )
                    _out << " and ";
                _out << (*sCons)->toString( 0, true, true );
            }
        }
        _out << endl;
    }
} // end namspace vs

