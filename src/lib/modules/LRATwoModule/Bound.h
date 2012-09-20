/*
 * Bound.h
 *
 *  Created on: Apr 24, 2012
 *      Author: cornflake
 */

#ifndef BOUND_H_
#define BOUND_H_

#include "Real.h"

using std::string;

namespace smtrat
{
    class Bound
    {
        public:
            //          Bound();
            //          Bound(Real bound);
            virtual ~Bound();

            Real getBound();

            void setBound( Real bound );

            void activate();

            void deactivate();

            bool isActive();

            virtual string toString() = 0;
            virtual bool checkBound( Real alpha, Real beta ) = 0;

        protected:
            bool activated;
            Real bound;
    };
}

#endif /* BOUND_H_ */
