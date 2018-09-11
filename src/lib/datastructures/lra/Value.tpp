/**
 * @file Value.tpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2012-04-05
 * @version 2014-10-01
 */

#pragma once

#include "Value.h"

namespace smtrat
{
    namespace lra
    {
        template<class T>
        Value<T>::Value():
            mMainPart( 0 ),
            mDeltaPart( 0 )
        {}

        template<class T>
        Value<T>::Value( const T& _num ):
            mMainPart( _num ),
            mDeltaPart( 0 )
        {}

        template<class T>
        Value<T>::Value( const T& _num1, const T& _num2 ):
            mMainPart( _num1 ),
            mDeltaPart( _num2 )
        {}

        template<class T>
        Value<T>::Value( const Value<T>& _orig ):
            mMainPart( _orig.mainPart() ),
            mDeltaPart( _orig.deltaPart() )
        {}

        template<class T>
        Value<T>::~Value(){}
        
        template<class T>
        Value<T>& Value<T>::operator=( const Value<T>& _value )
        {
            mMainPart = _value.mainPart();
            mDeltaPart = _value.deltaPart();
            return *this;
        }

        template<class T>
        Value<T> Value<T>::operator +( const Value<T>& _value ) const
        {
            T num1 = mMainPart + _value.mainPart();
            T num2 = mDeltaPart + _value.deltaPart();
            return Value( num1, num2 );
        }

        template<class T>
        void Value<T>::operator +=( const Value<T>& _value )
        {
            mMainPart += _value.mainPart();
            mDeltaPart += _value.deltaPart();
        }

        template<class T>
        Value<T> Value<T>::operator -( const Value<T>& _value ) const
        {
            T num1 = mMainPart - _value.mainPart();
            T num2 = mDeltaPart - _value.deltaPart();
            return Value( num1, num2 );
        }

        template<class T>
        void Value<T>::operator -=( const Value<T>& _value )
        {
            mMainPart -= _value.mainPart();
            mDeltaPart -= _value.deltaPart();
        }

        template<class T>
        Value<T> Value<T>::operator *( const T& a ) const
        {
            T num1 = a * mMainPart;
            T num2 = a * mDeltaPart;
            return Value( num1, num2 );
        }

        template<class T>
        void Value<T>::operator *=( const Value<T>& _value )
        {
            mMainPart *= _value.mainPart();
            mDeltaPart *= _value.deltaPart();
        }

        template<class T>
        void Value<T>::operator *=( const T& _a )
        {
            mMainPart *= _a;
            mDeltaPart *= _a;
        }

        template<class T>
        Value<T> Value<T>::operator /( const T& _a ) const
        {
            T num1 = T( mMainPart ) / _a;
            T num2 = T( mDeltaPart ) / _a;
            return Value( num1, num2 );
        }

        template<class T>
        void Value<T>::operator /=( const T& _a )
        {
            mMainPart /= _a;
            mDeltaPart /= _a;
        }

        template<class T>
        bool Value<T>::operator <( const Value<T>& _value ) const
        {
            if( mMainPart < _value.mainPart() )
            {
                return true;
            }
            else if( mMainPart == _value.mainPart() )
            {
                if( mDeltaPart < _value.deltaPart() )
                {
                    return true;
                }
            }
            return false;
        }

        template<class T>
        bool Value<T>::operator <=( const Value<T>& _value ) const
        {
            bool b = false;
            if( (mMainPart < _value.mainPart()) || (mMainPart == _value.mainPart() && mDeltaPart <= _value.deltaPart()) )
                b = true;
            return b;
        }

        template<class T>
        bool Value<T>::operator ==( const Value<T>& _value ) const
        {
            bool b = false;
            if( (mMainPart == _value.mainPart()) && (mDeltaPart == _value.deltaPart()) )
                b = true;
            return b;
        }
        
        template<class T>
        bool Value<T>::operator ==( const T& _a ) const
        {
            return (mMainPart == _a && mDeltaPart == 0 );
        }
        
        template<class T>
        bool Value<T>::operator <( const T& _a ) const
        {
            return (mMainPart < _a || (mMainPart == _a && mDeltaPart < 0 ));
        }
        
        template<class T>
        bool Value<T>::operator >( const T& _a ) const
        {
            return (mMainPart > _a || (mMainPart == _a && mDeltaPart > 0 ));
        }
        
        template<class T>
        bool Value<T>::operator <=( const T& _a ) const
        {
            return (mMainPart < _a || (mMainPart == _a && mDeltaPart <= 0 ));
        }
        
        template<class T>
        bool Value<T>::operator >=( const T& _a ) const
        {
            return (mMainPart > _a || (mMainPart == _a && mDeltaPart >= 0 ));
        }

        template<class T>
        const std::string Value<T>::toString() const
        {
            std::stringstream out;
            out << *this;
            return out.str();
        }
            
        template<class T1>
        std::ostream& operator<<( std::ostream& _out, const Value<T1>& _value )
        {
			return _out << _value.mainPart() << "+d*" << _value.deltaPart();
        }

        template<class T>
        void Value<T>::print( std::ostream& _out ) const
        {
            _out << "( " << mMainPart;
            _out << " + d * " << mDeltaPart << " )";
        }
    }    // end namspace lra
}    // end namspace smtrat

