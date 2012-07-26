/*
 * File:   Value.h
 * Author: x
 *
 * Created on April 30, 2012, 5:59 PM
 */

#ifndef _VALUE_H
#define _VALUE_H

#include <string.h>
#include <ginac/ginac.h>
#include <assert.h>

namespace lraone
{
    class Value
    {
        private:

            /**
             * Members.
             */
            GiNaC::numeric mMainPart;
            GiNaC::numeric mDeltaPart;

        public:
            Value();
            Value( GiNaC::numeric );
            Value( GiNaC::numeric, GiNaC::numeric );
            Value( int, int, int, int );
            Value( const Value& orig );
            virtual ~Value();

            Value operator +( Value& ) const;
            Value operator -( Value& ) const;
            Value operator *( GiNaC::numeric& ) const;
            Value operator /( GiNaC::numeric& ) const;
            bool operator <( const Value& ) const;
            bool operator >( const Value& ) const;
            bool operator <=( const Value& ) const;
            bool operator ==( const Value& ) const;

            void setmainP( int _num, int _denom )
            {
                mMainPart = GiNaC::numeric( _num ) / _denom;
            }

            void setInteger( int _int1 )
            {
                mMainPart  = _int1;
                mDeltaPart = 0;
            }

            GiNaC::numeric getmainP() const
            {
                return GiNaC::numeric( mMainPart );
            }

            void setdeltaP( int _num, int _denom )
            {
                mDeltaPart = GiNaC::numeric( _num ) / _denom;
            }

            GiNaC::numeric getdeltaP() const
            {
                return GiNaC::numeric( mDeltaPart );
            }

            std::string toString() const;
            void print( std::ostream& = std::cout ) const;
    };
}    // end namspace lra
#endif   /* _VALUE_H */
