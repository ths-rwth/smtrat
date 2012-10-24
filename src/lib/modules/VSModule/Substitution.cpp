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
 * @version 2011-12-05
 */

#include "Substitution.h"

using namespace std;
using namespace GiNaC;

namespace vs
{

    /**
    * Constructors:
    */
    Substitution::Substitution()
    {
        mpVariable 					= new string		( "RandomVariable" );
        mpVarAsEx                   = new ex( 0 );
        mpTerm 						= new SqrtEx			( )					;
        #ifdef VS_CUBIC_CASE
        mpMultiRootLessOcond		= new ex			( 0 )				;
        mpFirstZeroOfDerivOfOCond	= new SqrtEx			( )					;
        mpSecondZeroOfDerivOfOCond	= new SqrtEx			( )					;
        #endif
        mType						= ST_NORMAL									;
        mpOriginalConditions		= new ConditionSet	( )					;
    }


    Substitution::Substitution( const string& _variable, const GiNaC::ex& _varAsEx, const Substitution_Type& _type, const ConditionSet& _oConditions )
    {
        mpVariable 					= new string		( _variable )	;
        mpVarAsEx 					= new ex            ( _varAsEx )	;
        mpTerm 						= new SqrtEx		( )				;
        #ifdef VS_CUBIC_CASE
        mpMultiRootLessOcond		= new ex			( 0 )			;
        mpFirstZeroOfDerivOfOCond	= new SqrtEx			( )				;
        mpSecondZeroOfDerivOfOCond	= new SqrtEx			( )				;
        #endif
        mType						= Substitution_Type		( _type )		;
        mpOriginalConditions		= new ConditionSet	( _oConditions );
    }

    Substitution::Substitution( const string& _variable, const GiNaC::ex& _varAsEx, const SqrtEx& _term, const Substitution_Type& _type, const ConditionSet& _oConditions )
    {
        mpVariable 					= new string	( _variable )	;
        mpVarAsEx 					= new ex            ( _varAsEx )	;
        mpTerm 						= new SqrtEx		( _term )		;
        #ifdef VS_CUBIC_CASE
        mpMultiRootLessOcond		= new ex		( 0 )			;
        mpFirstZeroOfDerivOfOCond	= new SqrtEx		( )				;
        mpSecondZeroOfDerivOfOCond	= new SqrtEx		( )				;
        #endif
        mType						= Substitution_Type	( _type )		;
        mpOriginalConditions		= new ConditionSet	( _oConditions );
    }

    #ifdef VS_CUBIC_CASE
    Substitution::Substitution( const string& _variable, const ex& _multiRootLessOcond, const SqrtEx& _firstZeroOfDerivOfOCond, const SqrtEx& _secondZeroOfDerivOfOCond, const Substitution_Type& _type, const ConditionSet& _oConditions )
    {
        mpVariable 					= new string	( _variable )					;
        mpMultiRootLessOcond		= new ex		( _multiRootLessOcond )			;
        mpFirstZeroOfDerivOfOCond	= new SqrtEx		( _firstZeroOfDerivOfOCond )	;
        mpSecondZeroOfDerivOfOCond	= new SqrtEx		( _secondZeroOfDerivOfOCond )	;
        mType						= Substitution_Type	( _type )						;
        mpOriginalConditions		= new ConditionSet	( _oConditions )				;
        for( symtab::const_iterator var = _vars.begin();
            var!= _vars.end();
            ++var )
        {
            if( _multiRootLessOcond.has( ex( var->second ) ) )
            {
                mTermVariables.insert( make_pair( string( var->first ), var->second ) );
            }
        }
    }
    #endif

    Substitution::Substitution( const Substitution& _sub )
    {
        mpVariable 					= new string	( _sub.variable() )                     ;
        mpVarAsEx 					= new ex        ( _sub.varAsEx() )                      ;
        mType	   					= Substitution_Type	( _sub.type() )						;
        mpTerm 						= new SqrtEx		( _sub.term() )						;
        #ifdef VS_CUBIC_CASE
        mpMultiRootLessOcond		= new ex		( _sub.multiRootLessOcond() )		;
        mpFirstZeroOfDerivOfOCond	= new SqrtEx		( _sub.firstZeroOfDerivOfOCond() )	;
        mpSecondZeroOfDerivOfOCond	= new SqrtEx		( _sub.secondZeroOfDerivOfOCond() )	;
        #endif
        mpOriginalConditions		= new ConditionSet	( _sub.originalConditions() )		;
    }

    /**
    * Destructor:
    */
    Substitution::~Substitution()
    {
        delete mpVariable					;
        delete mpVarAsEx                    ;
        delete mpTerm						;
        #ifdef VS_CUBIC_CASE
        delete mpMultiRootLessOcond			;
        delete mpFirstZeroOfDerivOfOCond	;
        delete mpSecondZeroOfDerivOfOCond	;
        #endif
        delete mpOriginalConditions			;
    }

    /**
    * Methods:
    */

    /**
    * Valuates the substitution according to a heuristic.
    *
    * @return
    */
    unsigned Substitution::valuate() const
    {
        if( type()==ST_MINUS_INFINITY )
        {
            return 9;
        }
        else if( type()==ST_NORMAL )
        {
            if( termVariables().empty() )
            {
                return 8;
            }
            else
            {
                if( term().hasSqrt() )
                {
                    return 4;
                }
                else
                {
                    if( term().denominator().info( info_flags::rational ) )
                    {
                        return 6;
                    }
                    else
                    {
                        return 5;
                    }
                }
            }
        }
        else
        {
            if( termVariables().empty() )
            {
                return 7;
            }
            else
            {
                if( term().hasSqrt() )
                {
                    return 1;
                }
                else
                {
                    if( term().denominator().info( info_flags::rational ) )
                    {
                        return 3;
                    }
                    else
                    {
                        return 2;
                    }
                }
            }
        }
    }

    /**
    * Prints the substitution to an output stream.
    *
    * @param _out The output stream, where it should print.
    */
    void Substitution::print( ostream& _out ) const
    {
        switch( type() )
        {
            case ST_NORMAL:
            {
                _out << "[" << variable();
                _out << " -> " << term() << "]";
                break;
            }
            case ST_PLUS_EPSILON:
            {
                _out << "[" << variable();
                _out << " -> " << term() << " + epsilon]";
                break;
            }
            case ST_MINUS_INFINITY:
            {
                _out << "[" << variable() << " ->  -infinity]";
                break;
            }
            #ifdef VS_CUBIC_CASE
            case ST_SINGLE_CUBIC_ROOT:
            {
                _out << "["+ variable() + " -> its only root in ";
                _out << multiRootLessOcond() << "]";
                break;
            }
            case ST_TRIPLE_CUBIC_ROOT:
            {
                _out << "["+ variable() + " -> its three different roots in ";
                _out << multiRootLessOcond() << "]";
                break;
            }
            case ST_SINGLE_CUBIC_ROOT_PLUS_EPS:
            {
                _out << "["+ variable() + " -> its only root in ";
                _out << multiRootLessOcond() << " + epsilon]";
                break;
            }
            case ST_TRIPLE_CUBIC_ROOT_PLUS_EPS:
            {
                _out << "["+ variable() + " -> its three different roots in ";
                _out << multiRootLessOcond() << " + epsilon]";
                break;
            }
            #endif
            default:
            {
                cout << "Unknown substitution type!" << endl;
                assert( false );
            }
        }

        _out << "  {";
        for( ConditionSet::const_iterator oCond = originalConditions().begin();
            oCond!= originalConditions().end();
            ++oCond )
        {
            _out << " ( " << (**oCond).constraint().toString() << " )";
        }
        _out << " }";
    }

    /**
    * Gives the string representation of this substitution.
    *
    * @return The string representation of this substitution.
    */
    string	Substitution::toString() const
    {
        string stringRepresentation = "";
        switch( type() )
        {
            case ST_NORMAL:
            {
                stringRepresentation += "[" + variable();
                stringRepresentation += " -> ";
                ostringstream tempOStream;
                tempOStream << term();
                stringRepresentation += tempOStream.str();
                stringRepresentation += "]";
                break;
            }
            case ST_PLUS_EPSILON:
            {
                stringRepresentation += "[" + variable();
                stringRepresentation += " -> ";
                ostringstream tempOStream;
                tempOStream << term();
                stringRepresentation += tempOStream.str();
                stringRepresentation += " + epsilon]";
                break;
            }
            case ST_MINUS_INFINITY:
            {
                stringRepresentation += "[" + variable() + " ->  -infinity]";
                break;
            }
            #ifdef VS_CUBIC_CASE
            case ST_SINGLE_CUBIC_ROOT:
            {
                stringRepresentation += "["+ variable() + " -> its only root in ";
                ostringstream tempOStream;
                tempOStream << multiRootLessOcond();
                stringRepresentation += tempOStream.str();
                stringRepresentation += "]";
                break;
            }
            case ST_TRIPLE_CUBIC_ROOT:
            {
                stringRepresentation += "["+ variable() + " -> its three different roots in ";
                ostringstream tempOStream;
                tempOStream << multiRootLessOcond();
                stringRepresentation += tempOStream.str();
                stringRepresentation += "]";
                break;
            }
            case ST_SINGLE_CUBIC_ROOT_PLUS_EPS:
            {
                stringRepresentation += "["+ variable() + " -> its only root in ";
                ostringstream tempOStream;
                tempOStream << multiRootLessOcond();
                stringRepresentation += tempOStream.str();
                stringRepresentation += " + epsilon]";
                break;
            }
            case ST_TRIPLE_CUBIC_ROOT_PLUS_EPS:
            {
                stringRepresentation += "["+ variable() + " -> its three different roots in ";
                ostringstream tempOStream;
                tempOStream << multiRootLessOcond();
                stringRepresentation += tempOStream.str();
                stringRepresentation += " + epsilon]";
                break;
            }
            #endif
            default:
            {
                cout << "Unknown substitution type!" << endl;
                assert( false );
            }
        }
        return stringRepresentation;
    }

    /**
    * Gives the string representation of this substitution.
    *
    * @return The string representation of this substitution.
    */
    string	Substitution::toString2() const
    {
        string stringRepresentation = "";
        switch( type() )
        {
            case ST_NORMAL:
            {
                stringRepresentation += "[" + variable();
                stringRepresentation += " -> ";
                ostringstream tempOStream;
                tempOStream << term().expression();
                stringRepresentation += tempOStream.str();
                stringRepresentation += "]";
                break;
            }
            case ST_PLUS_EPSILON:
            {
                stringRepresentation += "[" + variable();
                stringRepresentation += " -> ";
                ostringstream tempOStream;
                tempOStream << term().expression();
                stringRepresentation += tempOStream.str();
                stringRepresentation += " + epsilon]";
                break;
            }
            case ST_MINUS_INFINITY:
            {
                stringRepresentation += "[" + variable() + " ->  -infinity]";
                break;
            }
            #ifdef VS_CUBIC_CASE
            case ST_SINGLE_CUBIC_ROOT:
            {
                stringRepresentation += "["+ variable() + " -> its only root in ";
                ostringstream tempOStream;
                tempOStream << multiRootLessOcond();
                stringRepresentation += tempOStream.str();
                stringRepresentation += "]";
                break;
            }
            case ST_TRIPLE_CUBIC_ROOT:
            {
                stringRepresentation += "["+ variable() + " -> its three different roots in ";
                ostringstream tempOStream;
                tempOStream << multiRootLessOcond();
                stringRepresentation += tempOStream.str();
                stringRepresentation += "]";
                break;
            }
            case ST_SINGLE_CUBIC_ROOT_PLUS_EPS:
            {
                stringRepresentation += "["+ variable() + " -> its only root in ";
                ostringstream tempOStream;
                tempOStream << multiRootLessOcond();
                stringRepresentation += tempOStream.str();
                stringRepresentation += " + epsilon]";
                break;
            }
            case ST_TRIPLE_CUBIC_ROOT_PLUS_EPS:
            {
                stringRepresentation += "["+ variable() + " -> its three different roots in ";
                ostringstream tempOStream;
                tempOStream << multiRootLessOcond();
                stringRepresentation += tempOStream.str();
                stringRepresentation += " + epsilon]";
                break;
            }
            #endif
            default:
            {
                cout << "Unknown substitution type!" << endl;
                assert( false );
            }
        }
        return stringRepresentation;
    }

    /**
    * Checks the equality of a given substitution with this substitution.
    *
    * @param _substitution The substitution to compare with.
    *
    * @return 	true	,if the given substitution is equal to this substitution;
    *			false	,otherwise.
    */
    bool Substitution::operator==( const Substitution& _substitution ) const
    {
        if( variable().compare( _substitution.variable() )==0 )
        {
            if( type()==_substitution.type() )
            {
                if( term()==_substitution.term() )
                {
                    #ifdef VS_CUBIC_CASE
                    if( multiRootLessOcond()==_substitution.multiRootLessOcond() )
                    {
                        return true;
                    }
                    else
                    {
                        return false;
                    }
                    #else
                    return true;
                    #endif
                }
                else
                {
                    return false;
                }
            }
            else
            {
                return false;
            }
        }
        else
        {
            return false;
        }
    }


    /**
    * Compares this substitution with the given substitution.
    *
    * @param _substitution The substitution to compare with.
    *
    * @return 	true	,if the given substitution is equal to this substitution;
    *			false	,otherwise.
    */
    bool Substitution::operator<( const Substitution& _substitution ) const
    {
        int varCompResult = variable().compare( _substitution.variable() );
        if( varCompResult<0 )
        {
            return true;
        }
        else if( varCompResult==0 )
        {
            if( type()<_substitution.type() )
            {
                return true;
            }
            else if( type()==_substitution.type() )
            {
                signed constPartCompResult = smtrat::Constraint::exCompare( term().constantPart(), termVariables(), _substitution.term().constantPart(), _substitution.termVariables() );
                if( constPartCompResult==-1 )
                {
                    return true;
                }
                else if( constPartCompResult==0 )
                {
                    signed factorCompResult = smtrat::Constraint::exCompare( term().factor(), termVariables(), _substitution.term().factor(), _substitution.termVariables() );
                    if( factorCompResult==-1 )
                    {
                        return true;
                    }
                    else if( factorCompResult==0 )
                    {
                        signed radicandCompResult = smtrat::Constraint::exCompare( term().radicand(), termVariables(), _substitution.term().radicand(), _substitution.termVariables() );
                        if( radicandCompResult==-1 )
                        {
                            return true;
                        }
                        else if( radicandCompResult==0 )
                        {
                            signed denominatorCompResult = smtrat::Constraint::exCompare( term().denominator(), termVariables(), _substitution.term().denominator(), _substitution.termVariables() );
                            if( denominatorCompResult==-1 )
                            {
                                return true;
                            }
                            #ifdef VS_CUBIC_CASE
                            else if( denominatorCompResult==0 )
                            {
                                if( multiRootLessOcond().constraint()<_substitution.multiRootLessOcond() )
                                {
                                    return true;
                                }
                                else
                                {
                                    return false;
                                }
                            }
                            else
                            {
                                return false;
                            }
                            #endif
                            else
                            {
                                return false;
                            }
                        }
                        else
                        {
                            return false;
                        }
                    }
                    else
                    {
                        return false;
                    }
                }
                else
                {
                    return false;
                }
            }
            else
            {
                return false;
            }
        }
        else
        {
            return false;
        }
    }

    /**
     * Prints a square root expression on an output stream.
     *
     * @param   _ostream    The output stream, on which to write.
     * @param   _sqrtEx     The square root expression to print.
     *
     * @return The representation of the square root expression on an output stream.
     */
    ostream& operator <<( ostream& _ostream, const Substitution& _substitution )
    {
        _ostream << _substitution.toString();
        return _ostream;
    }

    void Substitution::getVariables( const ex& _term, symtab& _variables )
    {
        if( _term.nops() > 1 )
        {
            for( const_iterator subterm = _term.begin(); subterm != _term.end(); ++subterm )
            {
                getVariables( *subterm, _variables );
            }
        }
        else if( is_exactly_a<symbol>( _term ) )
        {
            stringstream out;
            out << _term;
            _variables.insert( pair< string, symbol >( out.str(), ex_to<symbol>( _term ) ) );
        }
    }

} // end namspace vs

