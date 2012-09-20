/*
 * LowerBound.h
 *
 *  Created on: May 11, 2012
 *      Author: cornflake
 */

#ifndef LOWERBOUND_H_
#define LOWERBOUND_H_

#include "Bound.h"

namespace smtrat
{
    class LowerBound:
        public Bound
    {
        public:
            LowerBound();
            LowerBound( Real bound );
            virtual ~LowerBound();

            string toString();
            bool checkBound( Real alpha, Real beta );
    };

}    /* namespace smtrat */
#endif /* LOWERBOUND_H_ */
