/*
 * Author: Aliaksei Tsitovich <aliaksei.tsitovich@lu.unisi.ch>
 *      , Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>
 *
 * OpenSMT -- Copyright (C) 2007, Roberto Bruttomesso
 *
 * OpenSMT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * OpenSMT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
 */


#ifndef DELTA_H
#define DELTA_H

#include <ginac/ginac.h>
#include <ginac/flags.h>
#include <assert.h>

namespace lraone
{
    //
    // Class to keep the delta values and bounds values for the LAVar
    //
    class Delta
    {
        private:
            GiNaC::numeric* r;    // main value
            GiNaC::numeric* d;    // delta to keep track of < / <= difference
            bool            infinite;    // infinite bit
            bool            positive;    // +/- infinity bit

            inline bool isLess( const GiNaC::numeric& c ) const;    // basic function to use in comparison with GiNaC::numeric operator
            inline bool isGreater( const GiNaC::numeric& c ) const;    // basic function to use in comparison with GiNaC::numeric operator

        public:

            // possible types of initial Delta values;
            typedef enum { UPPER, LOWER, ZERO } deltaType;

            inline Delta( deltaType p );    // Default constructor (true for +inf; false for -inf)
            inline Delta( const GiNaC::numeric& v );    // Constructor for GiNaC::numeric delta
            inline Delta( const GiNaC::numeric& v, const GiNaC::numeric& d );    // Constructor for GiNaC::numeric delta with strict part
            inline Delta( const Delta& a );    // Copy constructor
            inline ~Delta();    // Destructor

            inline GiNaC::numeric& R() const;    // main value
            inline GiNaC::numeric& D() const;    // delta to keep track of < / <= difference
            inline bool hasDelta() const;    // TRUE is delta != 0
            inline bool isMinusInf() const;    // True if -inf
            inline bool isPlusInf() const;    // True if +inf
            inline bool isInf() const;    // True if inf (any)

            inline Delta& operator = ( const Delta& a );    // Assign operator

            // Comparisons overloading
            inline friend bool operator <( const Delta& a, const Delta& b );
            inline friend bool operator <=( const Delta& a, const Delta& b );
            inline friend bool operator >( const Delta& a, const Delta& b );
            inline friend bool operator >=( const Delta& a, const Delta& b );
            inline friend bool operator ==( const Delta& a, const Delta& b );
            inline friend bool operator !=( const Delta& a, const Delta& b );

            inline friend bool operator <( const Delta& a, const GiNaC::numeric& c );
            inline friend bool operator <=( const Delta& a, const GiNaC::numeric& c );
            inline friend bool operator >( const Delta& a, const GiNaC::numeric& c );
            inline friend bool operator >=( const Delta& a, const GiNaC::numeric& c );

            inline friend bool operator <( const GiNaC::numeric& c, const Delta& a );
            inline friend bool operator <=( const GiNaC::numeric& c, const Delta& a );
            inline friend bool operator >( const GiNaC::numeric& c, const Delta& a );
            inline friend bool operator >=( const GiNaC::numeric& c, const Delta& a );

            // Arithmetic overloadings
            inline friend Delta operator += ( Delta& a, const Delta& b );
            inline friend Delta operator -= ( Delta& a, const Delta& b );
            inline friend Delta operator -( const Delta& a, const Delta& b );
            inline friend Delta operator +( const Delta& a, const Delta& b );
            inline friend Delta operator *( const GiNaC::numeric& c, const Delta& a );
            inline friend Delta operator *( const Delta& a, const GiNaC::numeric& c );
            inline friend Delta operator /( const Delta& a, const GiNaC::numeric& c );

            void print( std::ostream& out ) const;    // print the Delta

            inline friend std::ostream& operator <<( std::ostream& out, const Delta& b )
            {
                b.print( out );
                return out;
            }

    };

    // main value
    inline GiNaC::numeric& Delta::R() const
    {
        assert( !infinite );
        assert( r );
        return *r;
    }

    // delta value (to keep track of < / <= difference)
    inline GiNaC::numeric& Delta::D() const
    {
        assert( !infinite );
        assert( d );
        return *d;
    }

    bool Delta::hasDelta() const
    {
        return !infinite && (D() != 0);
    }

    bool Delta::isPlusInf() const
    {
        return infinite && positive;
    }

    bool Delta::isMinusInf() const
    {
        return infinite &&!positive;
    }

    bool Delta::isInf() const
    {
        return infinite;
    }

    // Arithmetic operators definitions.
    Delta operator += ( Delta& a, const Delta& b )
    {
        assert( !a.isInf() );
        assert( !b.isInf() );
        if( !(a.isInf() || b.isInf()) )
        {
            *(a.r) += b.R();
            *(a.d) += b.D();
        }
        return a;
    }

    Delta operator -= ( Delta& a, const Delta& b )
    {
        assert( !a.isInf() );
        assert( !b.isInf() );
        if( !(a.isInf() || b.isInf()) )
        {
            *(a.r) -= b.R();
            *(a.d) -= b.D();
        }
        return a;
    }

    Delta operator -( const Delta& a, const Delta& b )
    {
        if( !(a.isInf() || b.isInf()) )
            return Delta( a.R() - b.R(), a.D() - b.D() );
        else
            return a;
    }

    Delta operator +( const Delta& a, const Delta& b )
    {
        if( !(a.isInf() || b.isInf()) )
            return Delta( a.R() + b.R(), a.D() + b.D() );
        else
            return a;
    }

    Delta operator *( const GiNaC::numeric& c, const Delta& a )
    {
        if( !(a.isInf()) )
            return Delta( c * a.R(), c * a.D() );
        else
            return a;
    }

    Delta operator *( const Delta& a, const GiNaC::numeric& c )
    {
        return c * a;
    }

    Delta operator /( const Delta& a, const GiNaC::numeric& c )
    {
        if( !(a.isInf()) )
        {
            GiNaC::numeric tempA = a.R() / c;
            assert( tempA.is_rational() );
            GiNaC::numeric tempB = a.D() / c;
            assert( tempB.is_rational() );
            return Delta( tempA, tempB );
        }
        else
            return a;
    }

    // Comparison operators definitions.
    // Most are implemented via calls to basic operators.
    //
    bool operator <( const Delta& a, const Delta& b )
    {
        if( a.isPlusInf() || b.isMinusInf() )
            return false;
        if( a.isMinusInf() || b.isPlusInf() || a.R() < b.R() || (a.R() == b.R() && a.D() < b.D()) )
            return true;
        else
            return false;
        //
        //  if( a.isPlusInf( ) )
        //    return false;
        //  else if( b.isMinusInf( ) )
        //    return false;
        //  else if( a.isMinusInf( ) )
        //    return true;
        //  else if( b.isPlusInf( ) )
        //    return true;
        //  else if( a.R( ) < b.R( ) )
        //    return true;
        //  else if( a.R( ) == b.R( ) && a.D( ) < b.D( ) )
        //    return true;
        //  else
        //    return false;
    }

    bool operator <=( const Delta& a, const Delta& b )
    {
        return !(b < a);
    }

    bool operator >( const Delta& a, const Delta& b )
    {
        return b < a;
    }

    bool operator >=( const Delta& a, const Delta& b )
    {
        return !(a < b);
    }

    bool operator ==( const Delta& a, const Delta& b )
    {
        if( (a.isInf() ^ b.isInf()) || (a.isPlusInf() && b.isMinusInf()) || (b.isPlusInf() && a.isMinusInf()) )
            return false;
        else if( (a.isPlusInf() && b.isPlusInf()) || (a.isMinusInf() && b.isMinusInf()) || (a.R() == b.R() && a.D() == b.D()) )
            return true;
        else
            return false;
    }

    bool operator !=( const Delta& a, const Delta& b )
    {
        return !(a == b);
    }

    bool operator <( const Delta& a, const GiNaC::numeric& c )
    {
        return a.isLess( c );
    }

    bool operator <=( const Delta& a, const GiNaC::numeric& c )
    {
        return !(a > c);
    }

    bool operator >( const Delta& a, const GiNaC::numeric& c )
    {
        return a.isGreater( c );
    }

    bool operator >=( const Delta& a, const GiNaC::numeric& c )
    {
        return !(a < c);
    }

    bool operator <( const GiNaC::numeric& c, const Delta& a )
    {
        return a > c;
    }

    bool operator <=( const GiNaC::numeric& c, const Delta& a )
    {
        return a >= c;
    }

    bool operator >( const GiNaC::numeric& c, const Delta& a )
    {
        return a < c;
    }

    bool operator >=( const GiNaC::numeric& c, const Delta& a )
    {
        return a <= c;
    }

    //
    // basic function to use in comparison with GiNaC::numeric
    //
    bool Delta::isLess( const GiNaC::numeric& c ) const
    {
        if( isPlusInf() )
            return false;
        else if( isMinusInf() )
            return true;
        else if( R() < c )
            return true;
        else if( R() == c && D() < 0 )
            return true;
        else
            return false;
    }

    //
    // basic function to use in comparison with GiNaC::numeric
    //
    bool Delta::isGreater( const GiNaC::numeric& c ) const
    {
        if( isMinusInf() )
            return false;
        else if( isPlusInf() )
            return true;
        else if( R() > c )
            return true;
        else if( R() == c && D() > 0 )
            return true;
        else
            return false;
    }

    //
    // Default constructor (true for +inf; false for -inf)
    //
    Delta::Delta( deltaType p = UPPER )
    {
        infinite = (p != ZERO);
        positive = (p == UPPER);
        if( !infinite )
        {
            r = new GiNaC::numeric( 0 );
            d = new GiNaC::numeric( 0 );
        }
        else
        {
            r = NULL;
            d = NULL;
        }
    }

    //
    // Constructor for GiNaC::numeric delta
    //
    Delta::Delta( const GiNaC::numeric& v )
    {
        infinite = false;
        positive = false;
        r        = new GiNaC::numeric( v );
        d        = new GiNaC::numeric( 0 );
    }

    //
    // Constructor for GiNaC::numeric delta with strict bit
    //
    Delta::Delta( const GiNaC::numeric& v_r, const GiNaC::numeric& v_d )
    {
        infinite = false;
        positive = false;
        r        = new GiNaC::numeric( v_r );
        d        = new GiNaC::numeric( v_d );
    }

    //
    // Copy constructor
    //
    Delta::Delta( const Delta& a )
    {
        infinite = a.infinite;
        positive = a.positive;
        if( !infinite )
        {
            r = new GiNaC::numeric( a.R() );
            d = new GiNaC::numeric( a.D() );
        }
        else
        {
            r = NULL;
            d = NULL;
        }
    }

    // Assign operator
    Delta& Delta::operator = ( const Delta& a )
    {
        if( this != &a )
        {
            if( !(infinite) )
            {
                delete (r);
                delete (d);
            }
            infinite = a.infinite;
            positive = a.positive;
            if( !(infinite) )
            {
                r = new GiNaC::numeric( a.R() );
                d = new GiNaC::numeric( a.D() );
            }
            else
            {
                r = NULL;
                d = NULL;
            }
        }
        return *this;
    }

    // Destructor
    Delta::~Delta()
    {
        if( !(infinite) )
        {
            delete (r);
            delete (d);
        }
    }

}    // end namspace vs

#endif
