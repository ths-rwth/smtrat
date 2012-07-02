/*
 * Real.h
 *
 *  Created on: Apr 30, 2012
 *      Author: cornflake
 */

#ifndef REAL_H_
#define REAL_H_

#include <ginac/ginac.h>
#include <sstream>

using GiNaC::numeric;
using std::string;

namespace smtrat
{
    class Real:
        public std:: pair<numeric, numeric>
    {
        public:
            Real();
            // sets real value to zero if not really real
            Real( numeric rational, bool reallyReal );
            Real( numeric rational, numeric real );
            virtual ~Real();

            numeric rationalPart() const;
            numeric realPart() const;

            void setRationalPart( numeric n );
            void setRealPart( numeric n );

            string toString();

            friend Real operator +( const Real&, const Real& );
            friend Real operator +( const numeric&, const Real& );
            friend Real operator +( const Real&, const numeric& );

            friend Real operator -( const Real&, const Real& );
            friend Real operator -( const numeric&, const Real& );
            friend Real operator -( const Real&, const numeric& );

            friend Real operator *( const Real&, const numeric& );
            friend Real operator *( const numeric&, const Real& );

            friend Real operator /( const Real&, const numeric& );
            friend Real operator /( const numeric&, const Real& );

            friend bool operator <=( const Real&, const Real& );
            friend bool operator >=( const Real&, const Real& );
            friend bool operator ==( const Real&, const Real& );

        private:
            Real addReal( const Real& toBeAdded ) const;
            Real addNumeric( const numeric& toBeAdded ) const;
            Real substractReal( const Real& toBeAdded ) const;
            Real substractNumeric( const numeric& toBeAdded ) const;
            Real multiplyWith( const numeric& factor ) const;
            Real divideBy( const numeric& divisor ) const;
            bool lowerEq( const Real& val2 ) const;
            bool isEqualTo( const Real& val2 ) const;
    };
}

#endif /* REAL_H_ */
