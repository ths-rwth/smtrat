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
                bool operator >( const Value<T>& _value ) const
                {
                    return _value < *this;
                }
                
                /**
                 * 
                 * @param _value
                 * @return 
                 */
                bool operator <=( const Value<T>& _value ) const;
                bool operator >=( const Value<T>& _value ) const
                {
                    return _value <= *this;
                }
                
                /**
                 * 
                 * @param _value
                 * @return 
                 */
                bool operator ==( const Value<T>& _value ) const;
                bool operator !=( const Value<T>& _value ) const
                {
                    return !(*this == _value);
                }
                
                /**
                 * 
                 * @param _a
                 * @return 
                 */
                bool operator ==( const T& _a ) const;
                bool operator !=( const T& _a ) const
                {
                    return !(*this == _a);
                }
                
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
                
                const Value<T>& abs_()
                {
                    if( *this < T(0) )
                        (*this) *= T( -1 );
                    return *this;
                }
                
                Value<T> abs() const
                {
                    if( *this < T(0) )
                        return (*this) * T( -1 );
                    else
                        return *this;
                }
                
                bool isZero() const
                {
                    return mMainPart == T(0) && mDeltaPart == T(0);
                }

                /**
                 * 
                 * @param _out
                 */
                void print( std::ostream& _out = std::cout ) const;
        };
		template <typename T1>
		std::ostream& operator<<( std::ostream& _out, const Value<T1>& _value );
    }    // end namspace lra
}    // end namspace smtrat

#include "Value.tpp"
