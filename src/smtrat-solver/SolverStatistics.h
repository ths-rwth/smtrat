#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat
{
    class SolverStatistics : public Statistics
    {
        std::size_t mNumberOfBranchingLemmas = 0;
       public:
         // Override Statistics::collect.
         void collect()
         {
            addKeyValuePair( "boolean_variables", carl::VariablePool::getInstance().nrVariables(carl::VariableType::VT_BOOL) );
            addKeyValuePair( "real_variables", carl::VariablePool::getInstance().nrVariables(carl::VariableType::VT_REAL) );
            addKeyValuePair( "integer_variables", carl::VariablePool::getInstance().nrVariables(carl::VariableType::VT_INT) );
            addKeyValuePair( "constraints", carl::constraintPool<Poly>().size() );
            addKeyValuePair( "non-linear_constraints", carl::constraintPool<Poly>().nrNonLinearConstraints() );
            addKeyValuePair( "maximal_degree", carl::constraintPool<Poly>().maxDegree() );
            addKeyValuePair( "number_of_learned_branching_lemmas", mNumberOfBranchingLemmas );
         }
        
        void addBranchingLemma()
        {
            ++mNumberOfBranchingLemmas;
        }
    };
}

#endif