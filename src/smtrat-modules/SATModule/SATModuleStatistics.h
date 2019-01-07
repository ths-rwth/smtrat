/** 
 * @file   SATstatistics.h
 *         Created on October 8, 2012, 11:07 PM
 * @author: Florian Corzilius
 *
 * 
 */

#pragma once

#include <smtrat-common/statistics/Statistics.h>

//#include <lib/utilities/stats/Statistics.h>
#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat
{
    class SATModuleStatistics : public Statistics
    {
    private:
        // Members.
        std::size_t mNrTotalVariablesBefore = 0;
        std::size_t mNrTotalVariablesAfter = 0;
        std::size_t mNrTseitinVariables = 0;
        std::size_t mNrClauses = 0;
        std::size_t mNrLearnedLemmas = 0;
        std::size_t mVarsWithPolarityTrue = 0;
        std::size_t mPropagations = 0;
        std::size_t mRestarts = 0;
        std::size_t mDecisions = 0;

    public:
        SATModuleStatistics( const std::string& _name ) : 
            Statistics( _name )
        {}

        ~SATModuleStatistics() {}

        void collect()
        {
            addKeyValuePair( "variables", mNrTotalVariablesBefore );
            addKeyValuePair( "introduced_variables", mNrTotalVariablesAfter-mNrTotalVariablesBefore );
            addKeyValuePair( "tseitin_variables", mNrTseitinVariables );
            addKeyValuePair( "variables_preferably_set_to_true", mVarsWithPolarityTrue );
            addKeyValuePair( "clauses", mNrClauses );
            addKeyValuePair( "lemmas_learned", mNrLearnedLemmas );
            addKeyValuePair( "propagations", mPropagations );
            addKeyValuePair( "decisions", mDecisions );
            addKeyValuePair( "restarts", mRestarts );
        }

        void lemmaLearned()
        {
            ++mNrLearnedLemmas;
        }

        void initialTrue()
        {
            ++mVarsWithPolarityTrue;
        }

        void propagate()
        {
            ++mPropagations;
        }

        void decide()
        {
            ++mDecisions;
        }

        void restart()
        {
            ++mRestarts;
        }
        
        size_t& rNrClauses()
        {
            return mNrClauses;
        }
        
        size_t& rNrTotalVariablesBefore()
        {
            return mNrTotalVariablesBefore;
        }
        
        size_t& rNrTotalVariablesAfter()
        {
            return mNrTotalVariablesAfter;
        }
        
        size_t& rNrTseitinVariables()
        {
            return mNrTseitinVariables;
        }

    };

}
#endif
