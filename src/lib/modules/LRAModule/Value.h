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
 * File:   Value.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2012-04-05
 * Created on November 14th, 2012
 */

#ifndef TLRA_VALUE_H
#define TLRA_VALUE_H

#include <string.h>
#include <assert.h>
#include <sstream>

namespace lra
{
    template<class T>
    class Value
    {
        private:

            /**
             * Members.
             */
            T mMainPart;
            T mDeltaPart;

        public:
            Value();
            Value( T );
            Value( T, T );
            Value( const Value<T>& orig );
            virtual ~Value();

            Value<T> operator +( const Value<T>& ) const;
            void operator +=( const Value<T>& );
            Value<T> operator -( const Value<T>& ) const;
            void operator -=( const Value<T>& );
            Value<T> operator *( const T& ) const;
            void operator *=( const Value<T>& );
            Value<T> operator /( const T& ) const;
            void operator /=( const T& );
            bool operator <( const Value<T>& ) const;
            bool operator >( const Value<T>& ) const;
            bool operator <=( const Value<T>& ) const;
            bool operator ==( const Value<T>& ) const;

            const std::string toString() const;

            const T& mainPart() const
            {
                return mMainPart;
            }

            const T& deltaPart() const
            {
                return mDeltaPart;
            }

            void print( std::ostream& = std::cout ) const;
    };

    template<class T>
    Value<T>::Value():
        mMainPart( 0 ),
        mDeltaPart( 0 )
    {}

    template<class T>
    Value<T>::Value( T _num ):
        mMainPart( _num ),
        mDeltaPart( 0 )
    {}

    template<class T>
    Value<T>::Value( T _num1, T _num2 ):
        mMainPart( _num1 ),
        mDeltaPart( _num2 )
    {}

    template<class T>
    Value<T>::Value( const Value<T>& orig ):
        mMainPart( orig.mainPart() ),
        mDeltaPart( orig.deltaPart() )
    {}

    template<class T>
    Value<T>::~Value(){}

    /**
     *
     * @param val
     * @return
     */
    template<class T>
    Value<T> Value<T>::operator +( const Value<T>& val ) const
    {
        T num1 = mMainPart + val.mainPart();
        T num2 = mDeltaPart + val.deltaPart();
        return Value( num1, num2 );
    }

    /**
     *
     * @param val
     */
    template<class T>
    void Value<T>::operator +=( const Value<T>& val )
    {
        mMainPart += val.mainPart();
        mDeltaPart += val.deltaPart();
    }

    /**
     *
     * @param val
     * @return
     */
    template<class T>
    Value<T> Value<T>::operator -( const Value<T>& val ) const
    {
        T num1 = mMainPart - val.mainPart();
        T num2 = mDeltaPart - val.deltaPart();
        return Value( num1, num2 );
    }

    /**
     *
     * @param val
     */
    template<class T>
    void Value<T>::operator -=( const Value<T>& val )
    {
        mMainPart -= val.mainPart();
        mDeltaPart -= val.deltaPart();
    }

    /**
     *
     * @param a
     * @return
     */
    template<class T>
    Value<T> Value<T>::operator *( const T& a ) const
    {
        T num1 = a * mMainPart;
        T num2 = a * mDeltaPart;
        return Value( num1, num2 );
    }

    /**
     *
     * @param val
     */
    template<class T>
    void Value<T>::operator *=( const Value<T>& val )
    {
        mMainPart *= val.mainPart();
        mDeltaPart *= val.deltaPart();
    }

    /**
     *
     * @param a
     * @return
     */
    template<class T>
    Value<T> Value<T>::operator /( const T& a ) const
    {
        T num1 = T( mMainPart ) / a;
        T num2 = T( mDeltaPart ) / a;
        return Value( num1, num2 );
    }

    /**
     *
     * @param a
     */
    template<class T>
    void Value<T>::operator /=( const T& a )
    {
        mMainPart /= a;
        mDeltaPart /= a;
    }

    /**
     *
     * @param _val
     * @return
     */
    template<class T>
    bool Value<T>::operator <( const Value<T>& _val ) const
    {
        if( mMainPart < _val.mainPart() )
        {
            return true;
        }
        else if( mMainPart == _val.mainPart() )
        {
            if( mDeltaPart < _val.deltaPart() )
            {
                return true;
            }
        }
        return false;
    }

    /**
     *
     * @param _val
     * @return
     */
    template<class T>
    bool Value<T>::operator >( const Value<T>& _val ) const
    {
        if( mMainPart > _val.mainPart() )
        {
            return true;
        }
        else if( mMainPart == _val.mainPart() )
        {
            if( mDeltaPart > _val.deltaPart() )
            {
                return true;
            }
        }
        return false;
    }

    /**
     *
     * @param val
     * @return
     */
    template<class T>
    bool Value<T>::operator <=( const Value<T>& val ) const
    {
        bool b = false;
        if( (mMainPart < val.mainPart()) || (mMainPart == val.mainPart() && mDeltaPart <= val.deltaPart()) )
            b = true;
        return b;
    }

    /**
     *
     * @param val
     * @return
     */
    template<class T>
    bool Value<T>::operator ==( const Value<T>& val ) const
    {
        bool b = false;
        if( (mMainPart == val.mainPart()) && (mDeltaPart == val.deltaPart()) )
            b = true;
        return b;
    }

    /**
     *
     * @return
     */
    template<class T>
    const std::string Value<T>::toString() const
    {
        std::stringstream out;
        out << mMainPart << "+d*" << mDeltaPart;
        return out.str();
    }

    /**
     *
     * @param _out
     */
    template<class T>
    void Value<T>::print( std::ostream& _out ) const
    {
        _out << "( " << mMainPart;
        _out << " + d * " << mDeltaPart << " )";
    }
}    // end namspace lra
#endif   /* TLRA_VALUE_H */
