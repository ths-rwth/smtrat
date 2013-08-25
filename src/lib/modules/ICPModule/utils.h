/*
 * File:   utils.h
 * Author: stefan
 *
 * Created on June 19, 2013, 4:06 PM
 */

#ifndef UTILS_H
#define UTILS_H

#include "../../Constraint.h"
#include <ginacra/ginacra.h>
#include "../../Formula.h"

namespace smtrat
{
    namespace icp
    {
        /**
        * Creates a new constraint from an existing interval
        * @param _interval
        * @return pair <lowerBoundConstraint*, upperBoundConstraint*>
        */
        std::pair<const Constraint*, const Constraint*> intervalToConstraint( const symbol& _var, const GiNaCRA::DoubleInterval _interval );

        /**
         * Checks whether the given constraint is a boundary constraint
         * @param _constraint
         * @return
         */
        bool isBound( const Constraint* _constraint );

        /**
         * Checks whether the given bound is a bound of the given variable.
         * @param _var
         * @param _constraint
         * @return
         */
        bool isBoundIn( const ex _var, const Constraint* _constraint );
        
        /**
        * Checks mIntervals if it contains an empty interval.
        * @return 
        */
        bool intervalBoxContainsEmptyInterval(const GiNaCRA::evaldoubleintervalmap& _intervals);
    }
}

#endif   /* UTILS_H */
