/*
 * Real.cpp
 *
 *  Created on: Apr 30, 2012
 *      Author: cornflake
 */

#include "Real.h"

using namespace std;
using namespace GiNaC;

namespace smtrat
{
    Real::Real():
        pair()
    {}

    Real::~Real()
    {
        // TODO Auto-generated destructor stub
    }

    Real::Real( numeric rational, bool reallyReal )
    {
        this->setRationalPart( rational );
        if( reallyReal )
        {
            this->setRealPart( numeric( 1 ) );
        }
        else
        {
            this->setRealPart( numeric( 0 ) );
        }
    }

    Real::Real( numeric rational, numeric real ):
        pair( rational, real )
    {}

    numeric Real::rationalPart() const
    {
        return this->first;
    }

    numeric Real::realPart() const
    {
        return this->second;
    }

    void Real::setRationalPart( numeric n )
    {
        this->first = n;
    }

    void Real::setRealPart( numeric n )
    {
        this->second = n;
    }

    string Real::toString()
    {
        string result = "";
        result        += "Real(";
        ostringstream sstream;
        sstream << this->rationalPart() << ", " << this->realPart();
        result += sstream.str();
        result += ")";
        return result;
    }

    bool operator ==( const Real& val1, const Real& val2 )
    {
        return val1.isEqualTo( val2 );
    }

    bool operator >=( const Real& val1, const Real& val2 )
    {
        return !val1.lowerEq( val2 );
    }

    bool operator <=( const Real& val1, const Real& val2 )
    {
        return val1.lowerEq( val2 );
    }

    Real operator +( const numeric& val1, const Real& val2 )
    {
        return val2.addNumeric( val1 );
    }

    Real operator +( const Real& val1, const numeric& val2 )
    {
        return val1.addNumeric( val2 );
    }

    Real operator +( const Real& val1, const Real& val2 )
    {
        return val1.addReal( val2 );
    }

    Real operator -( const Real& val1, const Real& val2 )
    {
        return val1.substractReal( val2 );
    }

    Real operator -( const numeric& val1, const Real& val2 )
    {
        return val2.substractNumeric( val1 );
    }

    Real operator -( const Real& val1, const numeric& val2 )
    {
        return val1.substractNumeric( val2 );
    }

    Real operator *( const Real& val1, const numeric& val2 )
    {
        return val1.multiplyWith( val2 );
    }

    Real operator *( const numeric& val1, const Real& val2 )
    {
        return val2.multiplyWith( val1 );
    }

    Real operator /( const Real& val1, const numeric& val2 )
    {
        return val1.divideBy( val2 );
    }

    Real operator /( const numeric& val1, const Real& val2 )
    {
        return val2.divideBy( val1 );
    }

    bool Real::isEqualTo( const Real& val2 ) const
    {
        numeric rational1 = this->rationalPart();
        numeric rational2 = val2.rationalPart();
        numeric real1     = this->realPart();
        numeric real2     = val2.realPart();
        return (rational1 == rational2 && real1 == real2);
    }

    bool Real::lowerEq( const Real& val2 ) const
    {
        numeric rational1 = this->rationalPart();
        numeric rational2 = val2.rationalPart();
        numeric real1     = this->realPart();
        numeric real2     = val2.realPart();
        if( rational1 < rational2 || (rational1 == rational2 && real1 <= real2) )
            return true;
        else
            return false;
    }

    Real Real::addReal( const Real& toBeAdded ) const
    {
        numeric rationalPart = this->rationalPart() + toBeAdded.rationalPart();
        numeric realPart     = this->realPart() + toBeAdded.realPart();
        return Real( rationalPart, realPart );
    }

    Real Real::addNumeric( const numeric& toBeAdded ) const
    {
        numeric rationalPart = this->rationalPart() + toBeAdded;
        return Real( rationalPart, this->realPart() );
    }

    Real Real::substractReal( const Real& toBeAdded ) const
    {
        numeric rationalPart = this->rationalPart() - toBeAdded.rationalPart();
        numeric realPart     = this->realPart() - toBeAdded.realPart();
        return Real( rationalPart, realPart );
    }

    Real Real::substractNumeric( const numeric& toBeAdded ) const
    {
        numeric rationalPart = this->rationalPart() - toBeAdded;
        return Real( rationalPart, realPart() );
    }

    Real Real::multiplyWith( const numeric& factor ) const
    {
        numeric rationalPart = this->rationalPart();
        numeric realPart     = this->realPart();
        return Real( factor * rationalPart, factor * realPart );
    }

    Real Real::divideBy( const numeric& divisor ) const
    {
        numeric rationalPart = this->rationalPart();
        numeric realPart     = this->realPart();
        return Real( rationalPart / divisor, realPart / divisor );

    }
}
