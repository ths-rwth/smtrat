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
 * @file Numeric.cpp
 * @author Florian Corzilius
 *
 * @version 2012-04-05
 * Created on November 14th, 2012
 */

#include "Numeric.h"

namespace tlra
{

    /**
     *
     * @param _num
     */
    Numeric::Numeric( const int _content )
    {
        mpContent = new GiNaC::numeric( _content );
    }

    /**
     *
     * @param _num
     */
    Numeric::Numeric( const GiNaC::numeric& _content )
    {
        mpContent = new GiNaC::numeric( _content );
    }

    /**
     *
     * @return
     */
    bool Numeric::isNegative() const
    {
        return mpContent->is_negative();
    }

    /**
     *
     * @return
     */
    bool Numeric::isPositive() const
    {
        return mpContent->is_positive();
    }

    /**
     *
     * @return
     */
    bool Numeric::isZero() const
    {
        return mpContent->is_zero();
    }

    /**
     *
     * @return
     */
    GiNaC::numeric Numeric::ginacNumeric() const
    {
        return *mpContent;
    }

    /**
     *
     * @param
     * @return
     */
    Numeric Numeric::operator +( const Numeric& _num ) const
    {
        Numeric result = *mpContent + _num.content();
        return result;
    }

    /**
     *
     * @param
     */
    void Numeric::operator +=( const Numeric& _num )
    {
        *mpContent += _num.content();
    }

    /**
     *
     * @param _num
     * @return
     */
    Numeric operator -( const Numeric& _num )
    {
        Numeric result = Numeric( -_num.content() );
        return result;
    }

    /**
     *
     * @param
     * @return
     */
    Numeric Numeric::operator -( const Numeric& _num ) const
    {
        Numeric result = *mpContent - _num.content();
        return result;
    }

    /**
     *
     * @param
     */
    void Numeric::operator -=( const Numeric& _num )
    {
        *mpContent -= _num.content();
    }

    /**
     *
     * @param
     * @return
     */
    Numeric Numeric::operator *( const Numeric& _num ) const
    {
        Numeric result = (*mpContent) * _num.content();
        return result;
    }

    /**
     *
     * @param
     */
    void Numeric::operator *=( const Numeric& _num )
    {
        *mpContent *= _num.content();
    }

    /**
     *
     * @param
     * @return
     */
    Numeric Numeric::operator /( const Numeric& _num ) const
    {
        Numeric result = *mpContent / _num.content();
        return result;
    }

    /**
     *
     * @param
     */
    void Numeric::operator /=( const Numeric& _num )
    {
        *mpContent /= _num.content();
    }

    /**
     *
     * @param
     * @return
     */
    bool Numeric::operator <( const Numeric& _num ) const
    {
        return *mpContent < _num.content();
    }

    /**
     *
     * @param
     * @return
     */
    bool Numeric::operator >( const Numeric& _num ) const
    {
        return *mpContent > _num.content();
    }

    /**
     *
     * @param
     * @return
     */
    bool Numeric::operator <=( const Numeric& _num ) const
    {
        return *mpContent <= _num.content();
    }

    /**
     *
     * @param
     * @return
     */
    bool Numeric::operator >=( const Numeric& _num ) const
    {
        return *mpContent >= _num.content();
    }

    /**
     *
     * @param
     * @return
     */
    bool Numeric::operator !=( const Numeric& _num ) const
    {
        return *mpContent != _num.content();
    }

    /**
     *
     * @param
     * @return
     */
    bool Numeric::operator ==( const Numeric& _num ) const
    {
        return *mpContent == _num.content();
    }

    /**
     *
     * @param
     * @param
     * @return
     */
    std::ostream& operator <<( std::ostream& _out, const Numeric& _num )
    {
        _out << GiNaC::ex( _num.content() );
        return _out;
    }
}    // end namspace tlra
