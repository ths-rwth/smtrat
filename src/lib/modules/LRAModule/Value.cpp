/*
 * File:   Value.cpp
 * Author: x
 *
 * Created on April 30, 2012, 5:59 PM
 */

#include <sstream>

#include "Value.h"
#include "assert.h"
#include "Bound.h"

using namespace std;

namespace lra
{
    Value::Value():
        mMainPart( 0 ),
        mDeltaPart( 0 )
    {}

    Value::Value( GiNaC::numeric _num ):
        mMainPart( 0 ),
        mDeltaPart( 0 )
    {
        assert( _num.is_rational() );
        mDeltaPart = 0;    // if we have one argument, delta part is 0
        mMainPart  = _num;
    }

    Value::Value( GiNaC::numeric _num1, GiNaC::numeric _num2 )
    {
        assert( _num1.is_rational() );
        assert( _num2.is_rational() );
        mDeltaPart = _num2;
        mMainPart  = _num1;
    }

    Value::Value( int _mainPnum, int _mainPdenom, int _deltaPnum, int _deltaPdenom )
    {
        mMainPart  = GiNaC::numeric( _mainPnum ) / _mainPdenom;
        mDeltaPart = GiNaC::numeric( _deltaPnum ) / _deltaPdenom;
    }

    Value::Value( const Value& orig )
    {
        mMainPart  = GiNaC::numeric( orig.getmainP() );
        mDeltaPart = GiNaC::numeric( orig.getdeltaP() );
    }

    Value::~Value(){}

    /**
     *
     * @param val
     * @return
     */
    Value Value::operator +( const Value& val ) const
    {
        GiNaC::numeric num1 = mMainPart + val.getmainP();
        GiNaC::numeric num2 = mDeltaPart + val.getdeltaP();
        return Value( num1, num2 );
    }

    /**
     *
     * @param val
     * @return
     */
    Value Value::operator -( const Value& val ) const
    {
        GiNaC::numeric num1 = mMainPart - val.getmainP();
        GiNaC::numeric num2 = mDeltaPart - val.getdeltaP();
        return Value( num1, num2 );
    }

    /**
     *
     * @param a
     * @return
     */
    Value Value::operator *( const GiNaC::numeric& a ) const
    {
        GiNaC::numeric num1 = a * mMainPart;
        GiNaC::numeric num2 = a * mDeltaPart;
        return Value( num1, num2 );
    }

    /**
     *
     * @param a
     * @return
     */
    Value Value::operator /( const GiNaC::numeric& a ) const
    {
        GiNaC::numeric num1 = GiNaC::numeric( mMainPart ) / a;
        GiNaC::numeric num2 = GiNaC::numeric( mDeltaPart ) / a;
        return Value( num1, num2 );
    }

    /**
     *
     * @param _val
     * @return
     */
    bool Value::operator <( const Value& _val ) const
    {
        if( mMainPart < _val.getmainP() )
        {
            return true;
        }
        else if( mMainPart == _val.getmainP() )
        {
            if( mDeltaPart < _val.getdeltaP() )
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
    bool Value::operator >( const Value& _val ) const
    {
        if( mMainPart > _val.getmainP() )
        {
            return true;
        }
        else if( mMainPart == _val.getmainP() )
        {
            if( mDeltaPart > _val.getdeltaP() )
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
    bool Value::operator <=( const Value& val ) const
    {
        bool b = false;
        if( (mMainPart < val.getmainP()) || (mMainPart == val.getmainP() && mDeltaPart <= val.getdeltaP()) )
            b = true;
        return b;
    }

    /**
     *
     * @param val
     * @return
     */
    bool Value::operator ==( const Value& val ) const
    {
        bool b = false;
        if( (mMainPart == val.getmainP()) && (mDeltaPart == val.getdeltaP()) )
            b = true;
        return b;
    }

    /**
     *
     * @return
     */
    const string Value::toString() const
    {
        stringstream out;
        out << mMainPart << "+d*" << mDeltaPart;
        return out.str();
    }

    /**
     *
     * @param _ostream
     * @param _value
     * @return
     */
//    ostream& operator <<( ostream& _ostream, const Value& _value )
//    {
//        _value.print( _ostream );
//        return _ostream;
//    }


    /**
     *
     * @param _out
     */
    void Value::print( ostream& _out ) const
    {
        _out << "( " << mMainPart;
        _out << " + d * " << mDeltaPart << " )";
    }
}    // end namspace lra

