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
 * Class to create a square root expression object.
 * @author Florian Corzilius
 * @since 2011-05-26
 * @version 2013-10-07
 */

#include "SqrtEx.h"

namespace vs
{
    using namespace std;

    SqrtEx::SqrtEx():
        mConstantPart( smtrat::ZERO_RATIONAL ),
        mFactor( smtrat::ZERO_RATIONAL ),
        mDenominator( smtrat::ONE_RATIONAL ),
        mRadicand( smtrat::ZERO_RATIONAL )
    {}

    SqrtEx::SqrtEx( smtrat::Poly&& _poly ):
        mConstantPart( std::move( _poly ) ),
        mFactor( smtrat::ZERO_RATIONAL ),
        mDenominator( smtrat::ONE_RATIONAL ),
        mRadicand( smtrat::ZERO_RATIONAL )
    {
        normalize();
    }

    SqrtEx::SqrtEx( smtrat::Poly&& _constantPart, smtrat::Poly&& _factor, smtrat::Poly&& _denominator, smtrat::Poly&& _radicand ):
        mConstantPart( std::move( _constantPart ) ),
        mFactor( _radicand.isZero() ? std::move( _radicand ) : std::move( _factor ) ),
        mDenominator( (mFactor.isZero() && mConstantPart.isZero()) ? smtrat::ONE_POLYNOMIAL : std::move( _denominator ) ),
        mRadicand( mFactor.isZero() ? mFactor : std::move( _radicand ) )
    {
        assert( !mDenominator.isZero() );
        assert( !mRadicand.isConstant() || mRadicand.isZero() || smtrat::ZERO_RATIONAL <= mRadicand.trailingTerm().coeff() );
        normalize();
    }

    void SqrtEx::normalize()
    {
//        cout << endl << __func__ << ": " << *this << endl;
        smtrat::Poly gcdA;
        if( mFactor.isZero() )
        {
            gcdA = mConstantPart;
        }
        else 
        {
            smtrat::Poly sqrtOfRadicand;
            if( mRadicand.sqrt( sqrtOfRadicand ) )
            {
                mConstantPart += mFactor * sqrtOfRadicand;
                mFactor = smtrat::ZERO_POLYNOMIAL;
                mRadicand = smtrat::ZERO_POLYNOMIAL;
            }
            else
            {
                assert( !radicand().isZero() );
                smtrat::Rational absOfLCoeff = abs( radicand().coprimeFactor() );
                smtrat::Rational sqrtResult;
                if( carl::sqrtp( absOfLCoeff, sqrtResult ) )
                {
                    mFactor *= (smtrat::Rational)1/sqrtResult;
                    mRadicand *= absOfLCoeff;
                }
            }
            if( mFactor.isZero() )
            {
                gcdA = mConstantPart;
            }
            else
            {
                if( mConstantPart.isZero() )
                {
                    gcdA = mFactor;
                }
                else
                {
                    smtrat::Rational ccConstantPart = mConstantPart.coprimeFactor();
                    smtrat::Poly cpConstantPart = mConstantPart * ccConstantPart;
                    smtrat::Rational ccFactor = mFactor.coprimeFactor();
                    smtrat::Poly cpFactor = mFactor * ccFactor;
                    gcdA = carl::gcd( cpConstantPart, cpFactor )*carl::gcd(ccConstantPart,ccFactor);
                }
            }
        }
        if( gcdA.isZero() ) return;
        smtrat::Rational ccGcdA = gcdA.coprimeFactor();
        smtrat::Poly cpGcdA = gcdA * ccGcdA;
        smtrat::Rational ccDenominator = mDenominator.coprimeFactor();
        smtrat::Poly cpDenominator = mDenominator * ccDenominator;
        gcdA = carl::gcd( cpGcdA, cpDenominator )*carl::gcd(ccGcdA,ccDenominator);
        // Make sure that the polynomial to divide by cannot be negative, otherwise the sign of the square root expression could change.
        if( !(gcdA == smtrat::ONE_POLYNOMIAL) && gcdA.definiteness() == carl::Definiteness::POSITIVE_SEMI )
        {
            if( !mConstantPart.isZero() )
            {
                mConstantPart.divideBy( gcdA, mConstantPart );
            }
            if( !mFactor.isZero() )
            {
                mFactor.divideBy( gcdA, mFactor );
            }
            mDenominator.divideBy( gcdA, mDenominator );
        }
        smtrat::Rational numGcd = smtrat::ZERO_RATIONAL;
        smtrat::Rational denomLcm = smtrat::ONE_RATIONAL;
        if( factor().isZero() )
        {
            if( !constantPart().isZero() )
            {
                smtrat::Rational cpOfConstantPart = constantPart().coprimeFactor();
                numGcd = carl::getNum( cpOfConstantPart );
                denomLcm = carl::getDenom( cpOfConstantPart );
            }
            else
            {
//                cout << "        to " << *this << endl;
                return; // Sqrt expression corresponds to 0.
            }
        }
        else
        {
            smtrat::Rational cpOfFactorPart = factor().coprimeFactor();
            if( constantPart().isZero() )
            {
                numGcd = carl::getNum( cpOfFactorPart );
                denomLcm = carl::getDenom( cpOfFactorPart );
            }
            else
            {
                smtrat::Rational cpOfConstantPart = constantPart().coprimeFactor();
                numGcd = carl::gcd( carl::getNum( cpOfConstantPart ), carl::getNum( cpOfFactorPart ) );
                denomLcm = carl::lcm( carl::getDenom( cpOfConstantPart ), carl::getDenom( cpOfFactorPart ) );
            }
        }
        assert( numGcd != smtrat::ZERO_RATIONAL );
        smtrat::Rational cpFactor = numGcd/denomLcm; 
        mConstantPart *= cpFactor;
        mFactor *= cpFactor;
        smtrat::Rational cpOfDenominator = denominator().coprimeFactor();
        mDenominator *= cpOfDenominator;
        smtrat::Rational sqrtExFactor = (denomLcm*carl::getNum( cpOfDenominator ))/(numGcd*carl::getDenom( cpOfDenominator ));
        mConstantPart *= carl::getNum( sqrtExFactor );
        mFactor *= carl::getNum( sqrtExFactor );
        mDenominator *= carl::getDenom( sqrtExFactor );
//        cout << "       to  " << *this << endl;
        //TODO: implement this method further
    }

    bool SqrtEx::operator==( const SqrtEx& _toCompareWith ) const
    {
        return    mRadicand == _toCompareWith.radicand() && mDenominator == _toCompareWith.denominator() 
               && mFactor == _toCompareWith.factor() && mConstantPart == _toCompareWith.constantPart();
    }

    SqrtEx& SqrtEx::operator=( const SqrtEx& _sqrtEx )
    {
        if( this != &_sqrtEx )
        {
            mConstantPart = _sqrtEx.constantPart();
            mFactor       = _sqrtEx.factor();
            mDenominator  = _sqrtEx.denominator();
            if( factor() == smtrat::ZERO_POLYNOMIAL )
                mRadicand = smtrat::ZERO_POLYNOMIAL;
            else
                mRadicand = _sqrtEx.radicand();
        }
        return *this;
    }

    SqrtEx& SqrtEx::operator=( const smtrat::Poly& _poly )
    {
        mConstantPart = _poly;
        mFactor       = smtrat::ZERO_POLYNOMIAL;
        mDenominator  = smtrat::ONE_POLYNOMIAL;
        mRadicand     = smtrat::ZERO_POLYNOMIAL;
        return *this;
    }

    SqrtEx operator+( const SqrtEx& _summandA, const SqrtEx& _summandB )
    {
        assert( !_summandA.hasSqrt() ||!_summandB.hasSqrt() || _summandA.radicand() == _summandB.radicand() );
        SqrtEx result = SqrtEx( _summandB.denominator() * _summandA.constantPart() + _summandB.constantPart() * _summandA.denominator(),
                         _summandB.denominator() * _summandA.factor() + _summandB.factor() * _summandA.denominator(),
                         _summandA.denominator() * _summandB.denominator(), _summandA.radicand() );
        return result;
    }

    SqrtEx operator-( const SqrtEx& _minuend, const SqrtEx& _subtrahend )
    {
        assert( !_minuend.hasSqrt() || !_subtrahend.hasSqrt() || _minuend.radicand() == _subtrahend.radicand() );
        SqrtEx result = SqrtEx( _subtrahend.denominator() * _minuend.constantPart() - _subtrahend.constantPart() * _minuend.denominator(),
                         _subtrahend.denominator() * _minuend.factor() - _subtrahend.factor() * _minuend.denominator(),
                         _minuend.denominator() * _subtrahend.denominator(), _minuend.radicand() );
        return result;
    }

    SqrtEx operator*( const SqrtEx& _factorA, const SqrtEx& _factorB )
    {
        assert( !_factorA.hasSqrt() || !_factorB.hasSqrt() || _factorA.radicand() == _factorB.radicand() );
        SqrtEx result = SqrtEx( _factorB.constantPart() * _factorA.constantPart() + _factorB.factor() * _factorA.factor() * _factorA.radicand(),
                         _factorB.constantPart() * _factorA.factor() + _factorB.factor() * _factorA.constantPart(),
                         _factorA.denominator() * _factorB.denominator(), _factorA.radicand() );
        return result;
    }

    SqrtEx operator/( const SqrtEx& _dividend, const SqrtEx& _divisor )
    {
        assert( !_divisor.hasSqrt() );
        SqrtEx result = SqrtEx( _dividend.constantPart() * _divisor.denominator(), _dividend.factor() * _divisor.denominator(),
                         _dividend.denominator() * _divisor.factor(), _dividend.radicand() );
        return result;
    }
    
    ostream& operator<<( ostream& _out, const SqrtEx& _substitution )
    {
        return (_out << _substitution.toString( true ) );
    }
    
    string SqrtEx::toString( bool _infix, bool _friendlyNames ) const
    {
        if( _infix )
        {
            bool complexNum = hasSqrt() && !mConstantPart.isConstant();
            string result = "";
            if( complexNum && !(mDenominator == smtrat::ONE_POLYNOMIAL) )
                result += "(";
            if( hasSqrt() )
            {
                if( mConstantPart.isConstant() )
                    result += mConstantPart.toString( true, _friendlyNames );
                else
                    result += "(" + mConstantPart.toString( true, _friendlyNames ) + ")";
                result += "+";
                if( mFactor.isConstant() )
                    result += mFactor.toString( true, _friendlyNames );
                else
                    result += "(" + mFactor.toString( true, _friendlyNames ) + ")";
                result += "*sqrt(" + mRadicand.toString( true, _friendlyNames ) + ")";
            }
            else
            {
                if( mConstantPart.isConstant() || mDenominator == smtrat::ONE_POLYNOMIAL )
                    result += mConstantPart.toString( true, _friendlyNames );
                else
                    result += "(" + mConstantPart.toString( true, _friendlyNames ) + ")";
            }
            if( !(mDenominator == smtrat::ONE_POLYNOMIAL) )
            {
                if( complexNum )
                    result += ")";
                result += "/";
                if( mDenominator.isConstant() )
                    result += mDenominator.toString( true, _friendlyNames );
                else
                    result += "(" + mDenominator.toString( true, _friendlyNames ) + ")";
            }
            return result;
        }
        else
        {
            string result = "(/ (+";
            result += mConstantPart.toString( false, _friendlyNames );
            result +=  " (*";
            result +=  mFactor.toString( false, _friendlyNames );
            result +=  " ";
            result +=  "(sqrt ";
            result +=  mRadicand.toString( false, _friendlyNames );
            result +=  "))) ";
            result +=  mDenominator.toString( false, _friendlyNames );
            result +=  ")";
            return result;
        }
    }
    
    bool SqrtEx::evaluate( smtrat::Rational& _result, const smtrat::EvalRationalMap& _evalMap, int _rounding ) const
    {
        smtrat::Poly radicandEvaluated = radicand().substitute( _evalMap );
        assert( radicandEvaluated.isConstant() );
        smtrat::Rational radicandValue = radicandEvaluated.constantPart();
        assert( radicandValue >= 0 );
        smtrat::Poly factorEvaluated = factor().substitute( _evalMap );
        assert( factorEvaluated.isConstant() );
        smtrat::Rational factorValue = factorEvaluated.constantPart();
        smtrat::Poly constantPartEvaluated = constantPart().substitute( _evalMap );
        assert( constantPartEvaluated.isConstant() );
        smtrat::Rational constantPartValue = constantPartEvaluated.constantPart();
        smtrat::Poly denomEvaluated = denominator().substitute( _evalMap );
        assert( denomEvaluated.isConstant() );
        smtrat::Rational denomValue = denomEvaluated.constantPart();
//        if( carl::isZero( denomValue ) ) exit(1236);
        assert( !carl::isZero( denomValue ) );
        // Check whether the resulting assignment is integer.
        bool rounded = true;
        smtrat::Rational sqrtExValue;
        if( !carl::sqrtp( radicandValue, sqrtExValue ) )
        {
            assert( _rounding != 0 );
            rounded = false;
            assert( factorValue != 0 );
            double dbSqrt = sqrt( carl::toDouble( radicandValue ) );
            sqrtExValue = carl::rationalize<smtrat::Rational>( dbSqrt ) ;
            // As there is no rational number representing the resulting square root we have to round.
            if( _rounding < 0 ) // If the result should round down in this case.
            {
                if( factorValue > 0 && (sqrtExValue*sqrtExValue) > radicandValue )
                {
                    // The factor of the resulting square root is positive, hence force rounding down.
                    dbSqrt = std::nextafter( dbSqrt, -INFINITY );
                    sqrtExValue = carl::rationalize<smtrat::Rational>( dbSqrt );
                    assert( !((sqrtExValue*sqrtExValue) > radicandValue) );
                }
                else if( factorValue < 0 && (sqrtExValue*sqrtExValue) < radicandValue )
                {
                    // The factor of the resulting square root is negative, hence force rounding up.
                    dbSqrt = std::nextafter( dbSqrt, INFINITY );
                    sqrtExValue = carl::rationalize<smtrat::Rational>( dbSqrt );
                    assert( !((sqrtExValue*sqrtExValue) < radicandValue) );
                }
            }
            else if( _rounding > 0 ) // If the result should round up in this case.
            {
                if( factorValue < 0 && (sqrtExValue*sqrtExValue) > radicandValue )
                {
                    // The factor of the resulting square root is negative, hence force rounding down.
                    dbSqrt = std::nextafter( dbSqrt, -INFINITY );
                    sqrtExValue = carl::rationalize<smtrat::Rational>( dbSqrt );
                    assert( !((sqrtExValue*sqrtExValue) > radicandValue) );
                }
                else if( factorValue > 0 && (sqrtExValue*sqrtExValue) < radicandValue )
                {
                    // The factor of the resulting square root is positive, hence force rounding up.
                    dbSqrt = std::nextafter( dbSqrt, INFINITY );
                    sqrtExValue = carl::rationalize<smtrat::Rational>( dbSqrt );
                    assert( !((sqrtExValue*sqrtExValue) < radicandValue) );
                }
            }
        }
        _result = (constantPartValue + factorValue * sqrtExValue) / denomValue;
        return rounded;
    }

    SqrtEx SqrtEx::subBySqrtEx( const smtrat::Poly& _substituteIn, const carl::Variable& _varToSubstitute, const SqrtEx& _substituteBy )
    {
        if( !_substituteIn.has( _varToSubstitute ) )
            return SqrtEx( _substituteIn );
        /*
         * We have to calculate the result of the substitution:
         *
         *                           q+r*sqrt{t}
         *        (a_n*x^n+...+a_0)[------------ / x]
         *                               s
         * being:
         *
         *      sum_{k=0}^n (a_k * (q+r*sqrt{t})^k * s^{n-k})
         *      ----------------------------------------------
         *                           s^n
         */
        smtrat::VarPolyInfo varInfo = _substituteIn.getVarInfo<true>( _varToSubstitute );
        const map<unsigned, smtrat::Poly>& coeffs = varInfo.coeffs();
        // Calculate the s^k:   (0<=k<=n)
        auto coeff = coeffs.begin();
        unsigned lastDegree = varInfo.maxDegree();
        vector<smtrat::Poly> sk;
        sk.push_back( smtrat::ONE_POLYNOMIAL );
        for( unsigned i = 1; i <= lastDegree; ++i )
        {
            // s^i = s^l * s^{i-l}
            sk.push_back( sk.back() * _substituteBy.denominator() );
        }
        // Calculate the constant part and factor of the square root of (q+r*sqrt{t})^k 
        vector<smtrat::Poly> qk;
        qk.push_back( _substituteBy.constantPart() );
        vector<smtrat::Poly> rk;
        rk.push_back( _substituteBy.factor() );
        // Let (q+r*sqrt{t})^l be (q'+r'*sqrt{t}) 
        // then (q+r*sqrt{t})^l+1  =  (q'+r'*sqrt{t}) * (q+r*sqrt{t})  =  ( q'*q+r'*r't  +  (q'*r+r'*q) * sqrt{t} )
        for( unsigned i = 1; i < lastDegree; ++i )
        {
            // q'*q+r'*r't
            qk.push_back( qk.back() * _substituteBy.constantPart() + rk.back() * _substituteBy.factor() * _substituteBy.radicand() );
            // q'*r+r'*q
            rk.push_back( rk.back() * _substituteBy.constantPart()  + qk.at( i - 1 ) * _substituteBy.factor() );
        }
        // Calculate the result:
        smtrat::Poly resFactor = smtrat::ZERO_POLYNOMIAL;
        smtrat::Poly resConstantPart = smtrat::ZERO_POLYNOMIAL;
        if( coeff->first == 0 )
        {
            resConstantPart += sk.back() * coeff->second;
            ++coeff;
        }
        for( ; coeff != coeffs.end(); ++coeff )
        {
            resConstantPart += coeff->second * qk.at( coeff->first - 1 ) * sk.at( lastDegree - coeff->first );
            resFactor       += coeff->second * rk.at( coeff->first - 1 ) * sk.at( lastDegree - coeff->first );
        }
        return SqrtEx( resConstantPart, resFactor, sk.back(), _substituteBy.radicand() );
    }
}    // end namspace vs

