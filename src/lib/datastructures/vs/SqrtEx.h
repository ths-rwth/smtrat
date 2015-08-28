/**
 * Class to create a square root expression object.
 * @author Florian Corzilius
 * @since 2011-05-26
 * @version 2013-10-22
 */

#pragma once

#include <iostream>
#include <assert.h>
#include "../../Common.h"

namespace vs
{
    class SqrtEx
    {
        private:
            /// The constant part c of this square root expression (c + f * sqrt(r))/d.
            smtrat::Poly mConstantPart;
            /// The factor f of this square root expression (c + f * sqrt(r))/d.
            smtrat::Poly mFactor;
            /// The denominator d of this square root expression (c + f * sqrt(r))/d.
            smtrat::Poly mDenominator;
            /// The radicand r of this square root expression (c + f * sqrt(r))/d.
            smtrat::Poly mRadicand;

        public:
            /**
             * Default Constructor. ( constructs (0 + 0 * sqrt( 0 )) / 1 )
             */
            SqrtEx();
            
            /**
             * Constructs a square root expression from a polynomial p leading to (p + 0 * sqrt( 0 )) / 1
             * @param _poly The polynomial to construct a square root expression for.
             */
            SqrtEx( smtrat::Poly&& _poly );
            SqrtEx( const smtrat::Poly& _poly ) : 
                SqrtEx::SqrtEx( std::move( smtrat::Poly( _poly ) ) )
            {}
            
            SqrtEx( carl::Variable::Arg _var ) : 
                SqrtEx( std::move( carl::makePolynomial<smtrat::Poly>( _var ) ) )
            {}
            
            template<typename P = smtrat::Poly, typename = typename std::enable_if<carl::needs_cache<P>::value>::type>
            SqrtEx( typename P::PolyType&& _poly ) : SqrtEx( std::move( carl::makePolynomial<P>( std::move(_poly) ) ) )
            {}
            
            /**
             * Constructs a square root expression from given constant part, factor, denominator and radicand.
             * @param _constantPart The constant part of the square root expression to construct.
             * @param _factor The factor of the square root expression to construct.
             * @param _denominator The denominator of the square root expression to construct.
             * @param _radicand The radicand of the square root expression to construct.
             */
            SqrtEx( const smtrat::Poly& _constantPart, const smtrat::Poly& _factor, const smtrat::Poly& _denominator, const smtrat::Poly& _radicand ):
                SqrtEx( std::move( smtrat::Poly( _constantPart ) ), std::move( smtrat::Poly( _factor ) ), std::move( smtrat::Poly( _denominator ) ), std::move( smtrat::Poly( _radicand ) ) )
            {}
            
            SqrtEx( smtrat::Poly&& _constantPart, smtrat::Poly&& _factor, smtrat::Poly&& _denominator, smtrat::Poly&& _radicand );
            
            /**
             * @return A constant reference to the constant part of this square root expression.
             */
            const smtrat::Poly& constantPart() const
            {
                return mConstantPart;
            }
            
            /**
             * @return A constant reference to the factor of this square root expression.
             */
            const smtrat::Poly& factor() const
            {
                return mFactor;
            }

            /**
             * @return A constant reference to the denominator of this square root expression.
             */
            const smtrat::Poly& denominator() const
            {
                return mDenominator;
            }

            /**
             * @return A constant reference to the radicand of this square root expression.
             */
            const smtrat::Poly& radicand() const
            {
                return mRadicand;
            }

            /**
             * @return true, if the square root expression has a non trivial radicand;
             *          false, otherwise.
             */
            bool hasSqrt() const
            {
                return mFactor != smtrat::Poly( smtrat::Rational( 0 ) );
            }

            /**
             * @return true, if there is no variable in this square root expression;
             *          false, otherwise.
             */
            bool isConstant() const
            {
                return mConstantPart.isConstant() && mDenominator.isConstant() && mFactor.isConstant() && mRadicand.isConstant();
            }

            /**
             * @return true, if there is no variable in this square root expression;
             *          false, otherwise.
             */
            bool isRational() const
            {
                return mConstantPart.isConstant() && mDenominator.isConstant() && mRadicand == smtrat::ZERO_POLYNOMIAL;
            }
            
        private:
            
            /**
             * Normalizes this object, that is extracts as much as possible from the radicand into the factor
             * and cancels the enumerator and denominator afterwards.
             */
            void normalize();
            
        public:
            
            /**
             * @return true, if the this square root expression corresponds to an integer value;
             *         false, otherwise.
             */
            bool isInteger() const
            {
                return radicand().isZero() && denominator() == smtrat::ONE_POLYNOMIAL && 
                       (constantPart().isZero() || (constantPart().isConstant() && carl::isInteger( constantPart().lcoeff() ) ) );
            }
            
            /**
             * @param _sqrtEx Square root expression to compare with.
             * @return  true, if this square root expression and the given one are equal;
             *          false, otherwise.
             */
            bool operator==( const SqrtEx& _toCompareWith ) const;
            
            /**
             * @param _sqrtEx A square root expression, which gets the new content of this square root expression.
             * @return A reference to this object.
             */
            SqrtEx& operator=( const SqrtEx& _sqrtEx );
            
            /**
             * @param _poly A polynomial, which gets the new content of this square root expression.
             * @return A reference to this object.
             */
            SqrtEx& operator=( const smtrat::Poly& _poly );
            
            /**
             * @param _summandA  First summand.
             * @param _summandB  Second summand.
             * @return The sum of the given square root expressions.
             */
            friend SqrtEx operator+( const SqrtEx& _summandA, const SqrtEx& _summandB );
            
            /**
             * @param _minuend  Minuend.
             * @param _subtrahend  Subtrahend.
             * @return The difference of the given square root expressions.
             */
            friend SqrtEx operator-( const SqrtEx& _minuend, const SqrtEx& _subtrahend );
      
            /**
             * @param _factorA  First factor.
             * @param _factorB  Second factor.
             * @return The product of the given square root expressions.
             */
            friend SqrtEx operator*( const SqrtEx& _factorA, const SqrtEx& _factorB );
            
            /**
             * @param _dividend  Dividend.
             * @param _divisor  Divisor.
             * @return The result of the first given square root expression divided by the second one
             *          Note that the second argument is not allowed to contain a square root.
             */
            friend SqrtEx operator/( const SqrtEx& _dividend, const SqrtEx& _divisor );
            
            /**
             * Prints the given square root expression on the given stream.
             * @param _out The stream to print on.
             * @param _sqrtEx The square root expression to print.
             * @return The stream after printing the square root expression on it.
             */
            friend std::ostream& operator<<( std::ostream& _out, const SqrtEx& _sqrtEx );
            
            /**
             * @param _infix A string which is printed in the beginning of each row.
             * @param _friendlyNames A flag that indicates whether to print the variables with their internal representation (false)
             *                        or with their dedicated names.
             * @return The string representation of this square root expression.
             */
            std::string toString( bool _infix = false, bool _friendlyNames = true ) const;
            
            bool evaluate( smtrat::Rational& _result, const smtrat::EvalRationalMap& _evalMap, int _rounding = 0 ) const;
            
            SqrtEx substitute( const smtrat::EvalRationalMap& _evalMap ) const;
            
            /**
             * Substitutes a variable in an expression by a square root expression, which results in a square root expression.
             * @param _substituteIn The polynomial to substitute in.
             * @param _varToSubstitute The variable to substitute.
             * @param _substituteBy The square root expression by which the variable gets substituted.
             * @return The resulting square root expression.
             */
            static SqrtEx subBySqrtEx( const smtrat::Poly& _substituteIn, const carl::Variable& _varToSubstitute, const SqrtEx& _substituteBy );
    };
}    // end namspace vs

namespace std
{
    /**
     * Implements std::hash for square root expressions.
     */
    template<>
    struct hash<vs::SqrtEx>
    {
    public:
        /**
         * @param _sqrtEx The square root expression to get the hash for.
         * @return The hash of the given square root expression.
         */
        size_t operator()( const vs::SqrtEx& _sqrtEx ) const 
        {
            return ((hash<smtrat::Poly>()(_sqrtEx.radicand()) ^ hash<smtrat::Poly>()(_sqrtEx.denominator())) ^ hash<smtrat::Poly>()(_sqrtEx.factor())) ^ hash<smtrat::Poly>()(_sqrtEx.constantPart());
        }
    };
} // namespace std

