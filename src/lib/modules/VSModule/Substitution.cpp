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
    Substitution::Substitution( const carl::Variable& _variable, const Type& _type, carl::PointerSet<Condition>&& _oConditions, smtrat::ConstraintsT&& _sideCondition ):
        mVariable( _variable ),
        mpTerm( new smtrat::SqrtEx() ),
        mType( _type ),
        mpTermVariables( nullptr ),
        mOriginalConditions( std::move( _oConditions ) ),
        mSideCondition( std::move(_sideCondition) )
    {
        if( mType == PLUS_EPSILON && mVariable.type() == carl::VariableType::VT_INT )
        {
            *mpTerm = *mpTerm + smtrat::SqrtEx(smtrat::ONE_POLYNOMIAL);
            mType = NORMAL;
        }
    }

    Substitution::Substitution( const carl::Variable& _variable, const smtrat::SqrtEx& _term, const Type& _type, carl::PointerSet<Condition>&& _oConditions, smtrat::ConstraintsT&& _sideCondition ):
        mVariable( _variable ),
        mpTerm( new smtrat::SqrtEx( _term ) ),
        mType( _type ),
        mpTermVariables( nullptr ),
        mOriginalConditions( std::move( _oConditions ) ),
        mSideCondition( std::move( _sideCondition ) )
    {
        if( mType == PLUS_EPSILON && mVariable.type() == carl::VariableType::VT_INT )
        {
            *mpTerm = *mpTerm + smtrat::SqrtEx(smtrat::ONE_POLYNOMIAL);
            mType = NORMAL;
        }
    }

    Substitution::Substitution( const Substitution& _sub ):
        mVariable( _sub.variable() ),
        mpTerm( new smtrat::SqrtEx( _sub.term() ) ),
        mType( _sub.type() ),
        mpTermVariables( _sub.mpTermVariables == nullptr ? nullptr : new carl::Variables( *_sub.mpTermVariables ) ),
        mOriginalConditions( _sub.originalConditions() ),
        mSideCondition( _sub.sideCondition() )
    {}

    Substitution::~Substitution()
    {
        if( mpTermVariables != nullptr )
            delete mpTermVariables;
        delete mpTerm;
    }

    unsigned Substitution::valuate( bool _preferMinusInf ) const
    {
        if( _preferMinusInf )
        {
            if( type() == MINUS_INFINITY || type() == PLUS_INFINITY )
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
        else
        {
            if( type() == MINUS_INFINITY || type() == PLUS_INFINITY )
                return 1;
            else if( type() == NORMAL )
            {
                if( term().isConstant() )
                    return 9;
                else
                {
                    if( term().hasSqrt() )
                        return 5;
                    else
                    {
                        if( term().denominator().isConstant() )
                            return 7;
                        else
                            return 6;
                    }
                }
            }
            else
            {
                if( term().isConstant() )
                    return 8;
                else
                {
                    if( term().hasSqrt() )
                        return 2;
                    else
                    {
                        if( term().denominator().isConstant() )
                            return 4;
                        else
                            return 3;
                    }
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

	ostream& operator<<(ostream& os, const Substitution& s) {
		os << "[" << s.variable() << " -> ";
		switch (s.type()) {
			case Substitution::NORMAL:
				os << s.term() << "]"; break;
			case Substitution::PLUS_EPSILON:
				os << s.term() << " + epsilon]"; break;
			case Substitution::MINUS_INFINITY:
				os << "-infinity]"; break;
			case Substitution::PLUS_INFINITY:
				os << "+infinity]"; break;
			case Substitution::INVALID:
				os << "invalid]"; break;
			default:
				assert(false);
				os << "unknown]"; break;
		}
		return os;
	}

    void Substitution::print( bool _withOrigins, bool _withSideConditions, ostream& _out, const string& _init ) const
    {
        _out << _init << *this;
        if( _withOrigins )
        {
            _out << " from {";
            for( auto oCond = originalConditions().begin(); oCond != originalConditions().end(); ++oCond )
            {
                if( oCond != originalConditions().begin() )
                    _out << ", ";
                _out << (**oCond).constraint();
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
                _out << *sCons;
            }
        }
        _out << endl;
    }
} // end namspace vs
