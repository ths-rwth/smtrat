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
 * @file Integer.cpp
 * @author Florian Corzilius
 *
 * @version 2012-04-05
 * Created on November 14th, 2012
 */

#include "Integer.h"

namespace tlra
{

    /**
     *
     * @param _num
     */
    Integer::Integer( const int _content )
    {
        if( _content < 0 )
        {
            mNumerator = -((unsigned)(_content));
            mDenominator = -1;
        }
        else
        {
            mNumerator = (unsigned)(_content);
            mDenominator = 1;
        }
    }

    /**
     *
     * @param _num
     */
    Integer::Integer( const GiNaC::numeric& _content )
    {
        if( _content.is_negative() )
        {
            mNumerator = (unsigned)(GiNaC::abs( _content.numer() ).to_int());
            mDenominator = -GiNaC::abs( _content.denom() ).to_int();
        }
        else
        {
            mNumerator = (unsigned)(GiNaC::abs( _content.numer() ).to_int());
            mDenominator = GiNaC::abs( _content.denom() ).to_int();
        }
    }

    /**
     *
     * @return
     */
    bool Integer::isNegative() const
    {
        return mDenominator < 0;
    }

    /**
     *
     * @return
     */
    bool Integer::isPositive() const
    {
        return mDenominator > 0;
    }

    /**
     *
     * @return
     */
    bool Integer::isZero() const
    {
        return mNumerator == 0;
    }

    /**
     *
     * @return
     */
    GiNaC::numeric Integer::ginacNumeric() const
    {
        return GiNaC::numeric(mNumerator)/mDenominator;
    }

    /**
     *
     * @param
     * @return
     */
    Integer Integer::operator +( const Integer& _num ) const
    {
        Integer result = mContent + _num.mContent;
        return result;
    }

    /**
     *
     * @param
     */
    void Integer::operator +=( const Integer& _num )
    {
        mContent += _num.mContent;
    }

    /**
     *
     * @param _num
     * @return
     */
    Integer operator -( const Integer& _num )
    {
        Integer result = Integer( - _num.mContent );
        return result;
    }

    /**
     *
     * @param
     * @return
     */
    Integer Integer::operator -( const Integer& _num ) const
    {
        Integer result = mContent - _num.mContent;
        return result;
    }

    /**
     *
     * @param
     */
    void Integer::operator -=( const Integer& _num )
    {
        mContent -= _num.mContent;
    }

    /**
     *
     * @param
     * @return
     */
    Integer Integer::operator *( const Integer& _num ) const
    {
        Integer result = mContent * _num.mContent;
        return result;
    }

    /**
     *
     * @param
     */
    void Integer::operator *=( const Integer& _num )
    {
        mContent *= _num.mContent;
    }

    /**
     *
     * @param
     * @return
     */
    Integer Integer::operator /( const Integer& _num ) const
    {
        Integer result = mContent / _num.mContent;
        return result;
    }

    /**
     *
     * @param
     */
    void Integer::operator /=( const Integer& _num )
    {
        mContent /= _num.mContent;
    }

    /**
     *
     * @param
     * @return
     */
    bool Integer::operator <( const Integer& _num ) const
    {
        return mContent < _num.mContent;
    }

    /**
     *
     * @param
     * @return
     */
    bool Integer::operator >( const Integer& _num ) const
    {
        return mContent > _num.mContent;
    }

    /**
     *
     * @param
     * @return
     */
    bool Integer::operator <=( const Integer& _num ) const
    {
        return mContent <= _num.mContent;
    }

    /**
     *
     * @param
     * @return
     */
    bool Integer::operator >=( const Integer& _num ) const
    {
        return mContent >= _num.mContent;
    }

    /**
     *
     * @param
     * @return
     */
    bool Integer::operator !=( const Integer& _num ) const
    {
        return mContent != _num.mContent;
    }

    /**
     *
     * @param
     * @return
     */
    bool Integer::operator ==( const Integer& _num ) const
    {
        return mContent == _num.mContent;
    }

    /**
     *
     * @param
     * @param
     * @return
     */
    std::ostream& operator <<( std::ostream& _out, const Integer& _num )
    {
        _out << GiNaC::ex( _num.mContent );
        return _out;
    }
}    // end namspace tlra
