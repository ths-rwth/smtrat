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
 * @file Value.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2012-04-05
 * @version 2014-10-01
 */

#pragma once

#include <string.h>
#include <assert.h>
#include <sstream>

namespace smtrat
{
    namespace lra
    {
        /**
         * 
         */
        template<class T>
        class Value
        {
            private:
                ///
                T mMainPart;
                ///
                T mDeltaPart;

            public:
                
                /**
                 * 
                 */
                Value();
                
                /**
                 * 
                 * @param _num
                 */
                Value( const T& _num );
                
                /**
                 * 
                 * @param _num1
                 * @param _num2
                 */
                Value( const T& _num1, const T& _num2 );
                
                /**
                 * 
                 * @param _orig
                 */
                Value( const Value<T>& _orig );
                
                /**
                 * 
                 */
                virtual ~Value();
                
                /**
                 * Copy the content of the given value to this one.
                 * @param _value The value to copy.
                 * @return This value after copying.
                 */
                Value<T>& operator=( const Value<T>& _value );
                
                /**
                 * 
                 * @param _value
                 * @return 
                 */
                Value<T> operator +( const Value<T>& _value ) const;
                
                /**
                 * 
                 * @param _value
                 */
                void operator +=( const Value<T>& _value );
                
                /**
                 * 
                 * @param _value
                 * @return 
                 */
                Value<T> operator -( const Value<T>& _value ) const;
                
                /**
                 * 
                 * @param _value
                 */
                void operator -=( const Value<T>& _value );
                
                /**
                 * 
                 * @param _a
                 * @return 
                 */
                Value<T> operator *( const T& _a ) const;
                
                /**
                 * 
                 * @param _value
                 */
                void operator *=( const Value<T>& _value );
                
                /**
                 * 
                 * @param _a
                 */
                void operator *=( const T& _a );
                
                /**
                 * 
                 * @param _a
                 * @return 
                 */
                Value<T> operator /( const T& _a ) const;
                
                /**
                 * 
                 * @param _a
                 */
                void operator /=( const T& _a );
                
                /**
                 * 
                 * @param _value
                 * @return 
                 */
                bool operator <( const Value<T>& _value ) const;
                
                /**
                 * 
                 * @param _value
                 * @return 
                 */
                bool operator >( const Value<T>& _value ) const;
                
                /**
                 * 
                 * @param _value
                 * @return 
                 */
                bool operator <=( const Value<T>& _value ) const;
                
                /**
                 * 
                 * @param _value
                 * @return 
                 */
                bool operator ==( const Value<T>& _value ) const;
                
                /**
                 * 
                 * @param _a
                 * @return 
                 */
                bool operator ==( const T& _a ) const;
                
                /**
                 * 
                 * @param _a
                 * @return 
                 */
                bool operator <( const T& _a ) const;
                
                /**
                 * 
                 * @param _a
                 * @return 
                 */
                bool operator >( const T& _a ) const;
                
                /**
                 * 
                 * @param _a
                 * @return 
                 */
                bool operator <=( const T& _a ) const;
                
                /**
                 * 
                 * @param _a
                 * @return 
                 */
                bool operator >=( const T& _a ) const;

                /**
                 * 
                 * @return 
                 */
                const std::string toString() const;
                
                /**
                 * @param _out
                 * @param _value
                 * @return 
                 */
                template <typename T1> friend std::ostream& operator<<( std::ostream& _out, const Value<T1>& _value );

                /**
                 * @return 
                 */
                const T& mainPart() const
                {
                    return mMainPart;
                }

                /**
                 * @return 
                 */
                const T& deltaPart() const
                {
                    return mDeltaPart;
                }

                /**
                 * 
                 * @param _out
                 */
                void print( std::ostream& _out = std::cout ) const;
        };
    }    // end namspace lra
}    // end namspace smtrat

#include "Value.tpp"
