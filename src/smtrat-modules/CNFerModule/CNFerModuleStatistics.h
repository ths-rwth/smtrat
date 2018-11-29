/** 
 * @file   CNFerModuleStatistics.h
 * @author: Florian Corzilius
 *
 * 
 */

#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include "../../utilities/stats/Statistics.h"

namespace smtrat
{
    class CNFerModuleStatistics : public Statistics
    {
    private:
        // Members.
        size_t mBooleanComplexity;
        size_t mNrOfArithVariables;
        size_t mNrOfBoolVariables;

    public:
        CNFerModuleStatistics( const std::string& _name ) : 
            Statistics( _name, this ),
            mBooleanComplexity( 1 ),
            mNrOfArithVariables( 0 ),
            mNrOfBoolVariables( 0 )
        {}

        ~CNFerModuleStatistics() {}

        void collect()
        {
            Statistics::addKeyValuePair( "boolean_complexity", mBooleanComplexity );
            Statistics::addKeyValuePair( "nr_of_arith_variables", mNrOfArithVariables );
            Statistics::addKeyValuePair( "nr_of_bool_variables", mNrOfBoolVariables );
        }

        void addClauseOfSize(size_t _clauseSize)
        {
            unsigned targetlevel = 0;
            while (_clauseSize >>= 1) ++targetlevel;
            mBooleanComplexity += targetlevel;
        }
        
        size_t& nrOfArithVariables()
        {
            return mNrOfArithVariables;
        }
        
        size_t& nrOfBoolVariables()
        {
            return mNrOfBoolVariables;
        }

    };

}
#endif
