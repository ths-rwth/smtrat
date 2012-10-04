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
        mMainPart( _num ),
        mDeltaPart( 0 )
    {}

    Value::Value( GiNaC::numeric _num1, GiNaC::numeric _num2 ):
        mMainPart( _num1 ),
        mDeltaPart( _num2 )
    {}

    Value::Value( const Value& orig ):
        mMainPart( orig.mainPart() ),
        mDeltaPart( orig.deltaPart() )
    {}

    Value::~Value(){}

    /**
     *
     * @param val
     * @return
     */
    Value Value::operator +( const Value& val ) const
    {
        GiNaC::numeric num1 = mMainPart + val.mainPart();
        GiNaC::numeric num2 = mDeltaPart + val.deltaPart();
        return Value( num1, num2 );
    }

    /**
     *
     * @param val
     */
    void Value::operator +=( const Value& val )
    {
        mMainPart += val.mainPart();
        mDeltaPart += val.deltaPart();
    }

    /**
     *
     * @param val
     * @return
     */
    Value Value::operator -( const Value& val ) const
    {
        GiNaC::numeric num1 = mMainPart - val.mainPart();
        GiNaC::numeric num2 = mDeltaPart - val.deltaPart();
        return Value( num1, num2 );
    }

    /**
     *
     * @param val
     */
    void Value::operator -=( const Value& val )
    {
        mMainPart -= val.mainPart();
        mDeltaPart -= val.deltaPart();
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
     * @param val
     */
    void Value::operator *=( const Value& val )
    {
        mMainPart *= val.mainPart();
        mDeltaPart *= val.deltaPart();
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
     * @param a
     */
    void Value::operator /=( const GiNaC::numeric& a )
    {
        mMainPart /= a;
        mDeltaPart /= a;
    }

    /**
     *
     * @param _val
     * @return
     */
    bool Value::operator <( const Value& _val ) const
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
    bool Value::operator >( const Value& _val ) const
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
    bool Value::operator <=( const Value& val ) const
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
    bool Value::operator ==( const Value& val ) const
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

