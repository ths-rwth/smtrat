/*
 * File:   utils.h
 * Author: stefan
 *
 * Created on June 19, 2013, 4:06 PM
 */

#pragma once

#include "../LRAModule/LRAModule.h"
#include <carl-arith/numbers/numbers.h>
#include <smtrat-common/smtrat-common.h>

namespace smtrat
{    
    namespace icp
    {
        /**
         * Obtains the non-linear monomials of the given polynomial.
         * @param _expr The polynomial to obtain the non-linear monomials for.
         * @return The non-linear monomials.
         */
        std::vector<Poly> getNonlinearMonomials( const Poly& _expr );
        
        /**
        * Creates a new constraint from an existing interval
        * @param _interval
        * @return pair <lowerBoundConstraint*, upperBoundConstraint*>
        */
        std::pair<ConstraintT, ConstraintT> intervalToConstraint( const Poly& _lhs, const smtrat::DoubleInterval _interval );
        
        /**
        * Checks mIntervals if it contains an empty interval.
        * @return 
        */
        bool intervalBoxContainsEmptyInterval(const EvalDoubleIntervalMap& _intervals);
        
        
        const LRAModule<LRASettings1>::LRAVariable* getOriginalLraVar ( carl::Variable::Arg _var, const LRAModule<LRASettings1>& _lra );
        
    }
}
