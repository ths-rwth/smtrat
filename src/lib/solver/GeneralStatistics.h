#pragma once

#include "../config.h"
#ifdef SMTRAT_DEVOPTION_Statistics
#include "../Common.h"
#include "../utilities/stats/Statistics.h"

namespace smtrat
{
    class GeneralStatistics : public Statistics
    {
       public:
         // Override Statistics::collect.
         void collect()
         {
            Statistics::addKeyValuePair( "boolean_variables", carl::VariablePool::getInstance().nrVariables(carl::VariableType::VT_BOOL) );
            Statistics::addKeyValuePair( "real_variables", carl::VariablePool::getInstance().nrVariables(carl::VariableType::VT_REAL) );
            Statistics::addKeyValuePair( "integer_variables", carl::VariablePool::getInstance().nrVariables(carl::VariableType::VT_INT) );
            Statistics::addKeyValuePair( "constraints", carl::constraintPool<Poly>().size() );
            Statistics::addKeyValuePair( "non-linear_constraints", carl::constraintPool<Poly>().nrNonLinearConstraints() );
            Statistics::addKeyValuePair( "maximal_degree", carl::constraintPool<Poly>().maxDegree() );
         }

        GeneralStatistics() : Statistics("General", this)
        {}
    };
}

#endif