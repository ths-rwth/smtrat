/*
 * UpperBound.h
 *
 *  Created on: May 11, 2012
 *      Author: cornflake
 */

#ifndef UPPERBOUND_H_
#define UPPERBOUND_H_

#include "Bound.h"

namespace smtrat
{
    class UpperBound:
        public Bound
    {
        public:
            UpperBound();
            UpperBound( Real bound );
            virtual ~UpperBound();

            string toString();
            bool checkBound( Real alpha, Real beta );
    };

}    /* namespace smtrat */
#endif /* UPPERBOUND_H_ */
