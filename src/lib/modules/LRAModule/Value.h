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

namespace lra
{
    // TODO: Take a faster datatype the GiNaC::numeric.
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
            Value( const Value& orig );
            virtual ~Value();

            Value operator +( const Value& ) const;
            void operator +=( const Value& );
            Value operator -( const Value& ) const;
            void operator -=( const Value& );
            Value operator *( const GiNaC::numeric& ) const;
            void operator *=( const Value& );
            Value operator /( const GiNaC::numeric& ) const;
            void operator /=( const GiNaC::numeric& );
            bool operator <( const Value& ) const;
            bool operator >( const Value& ) const;
            bool operator <=( const Value& ) const;
            bool operator ==( const Value& ) const;

            const std::string toString() const;

            const GiNaC::numeric& mainPart() const
            {
                return mMainPart;
            }

            const GiNaC::numeric& deltaPart() const
            {
                return mDeltaPart;
            }

            void print( std::ostream& = std::cout ) const;
    };
}    // end namspace lra
#endif   /* _VALUE_H */
