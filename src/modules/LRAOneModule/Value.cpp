/*
 * File:   Value.cpp
 * Author: x
 *
 * Created on April 30, 2012, 5:59 PM
 */

#include "Value.h"
#include "assert.h"

using namespace std;

namespace lraone
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
        this->mDeltaPart = 0;    // if we have one argument, delta part is 0
        this->mMainPart  = _num;
    }

    Value::Value( GiNaC::numeric _num1, GiNaC::numeric _num2 )
    {
        assert( _num1.is_rational() );
        assert( _num2.is_rational() );
        this->mDeltaPart = _num2;
        this->mMainPart  = _num1;
    }

    Value::Value( int _mainPnum, int _mainPdenom, int _deltaPnum, int _deltaPdenom )
    {
        this->mMainPart  = GiNaC::numeric( _mainPnum ) / _mainPdenom;
        this->mDeltaPart = GiNaC::numeric( _deltaPnum ) / _deltaPdenom;
    }

    Value::Value( const Value& orig )
    {
        this->mMainPart  = GiNaC::numeric( orig.getmainP() );
        this->mDeltaPart = GiNaC::numeric( orig.getdeltaP() );
    }

    Value::~Value(){}

    /**
     *
     * @param val
     * @return
     */
    Value Value::operator +( Value& val ) const
    {
        GiNaC::numeric num1 = this->mMainPart + val.getmainP();
        GiNaC::numeric num2 = this->mDeltaPart + val.getdeltaP();
        return Value( num1, num2 );
    }

    /**
     *
     * @param val
     * @return
     */
    Value Value::operator -( Value& val ) const
    {
        GiNaC::numeric num1 = this->mMainPart - val.getmainP();
        GiNaC::numeric num2 = this->mDeltaPart - val.getdeltaP();
        return Value( num1, num2 );
    }

    /**
     *
     * @param a
     * @return
     */
    Value Value::operator *( GiNaC::numeric& a ) const
    {
        GiNaC::numeric num1 = a * this->mMainPart;
        GiNaC::numeric num2 = a * this->mDeltaPart;
        return Value( num1, num2 );
    }

    /**
     *
     * @param a
     * @return
     */
    Value Value::operator /( GiNaC::numeric& a ) const
    {
        GiNaC::numeric num1 = GiNaC::numeric( this->mMainPart ) / a;
        GiNaC::numeric num2 = GiNaC::numeric( this->mDeltaPart ) / a;
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
        if( (this->mMainPart < val.getmainP()) || (this->mMainPart == val.getmainP() && this->mDeltaPart <= val.getdeltaP()) )
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
        if( (this->mMainPart == val.getmainP()) && (this->mDeltaPart == val.getdeltaP()) )
            b = true;
        return b;
    }

    /**
     *
     * @param _out
     */
    void Value::print( ostream& _out ) const
    {
        _out << "( " << this->mMainPart;
        _out << " + d * " << this->mDeltaPart << " )";
    }
}    // end namspace lra

