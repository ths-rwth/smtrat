/*
 * File:   utils.h
 * Author: stefan
 *
 * Created on June 19, 2013, 4:06 PM
 */

#pragma once

#include "../../Constraint.h"
#include "../../Formula.h"
#include "../LRAModule/LRAModule.h"
#include <carl/numbers/operations.h>

namespace smtrat
{
    namespace icp
    {
        /**
        * Determines, if the given expression is linear
        * @param _constr Needed to associate linearization with constraint
        * @param _expr Expression, which is checked
        * @return true, if expression is linear
        */
        bool isLinear( const Constraint* _constr, const Polynomial& _expr, FastMap<Polynomial, const Constraint*>& _tempMonomes );
        
        /**
        * Creates a new constraint from an existing interval
        * @param _interval
        * @return pair <lowerBoundConstraint*, upperBoundConstraint*>
        */
        std::pair<const Constraint*, const Constraint*> intervalToConstraint( const carl::Variable& _var, const carl::DoubleInterval _interval );

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
        bool isBoundIn( const carl::Variable::Arg _var, const Constraint* _constraint );
        
        /**
        * Checks mIntervals if it contains an empty interval.
        * @return 
        */
        bool intervalBoxContainsEmptyInterval(const EvalDoubleIntervalMap& _intervals);
        
        
        const smtrat::lra::Variable<lra::Numeric>* getOriginalLraVar ( const carl::Variable::Arg _var, LRAModule& _lra );
        
    }
}
