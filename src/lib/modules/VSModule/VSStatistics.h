/** 
 * @file   VSStatistics.h
 *         Created on April 20, 2016, 11:15 PM
 * @author: Florian Corzilius
 *
 * 
 */

#pragma once

#include "../../utilities/stats/Statistics.h"
#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat
{
    class VSStatistics : public Statistics
    {
    private:
        // Members.
        size_t mNrOfBranchingLemmas;

    public:
        VSStatistics( const std::string& _name ) : 
            Statistics( _name, this ),
            mNrOfBranchingLemmas( 0 )
        {}

        ~VSStatistics() {}

        void collect()
        {
            Statistics::addKeyValuePair( "number_of_branching_lemmas", mNrOfBranchingLemmas );
        }

        void branch()
        {
            ++mNrOfBranchingLemmas;
        }

    };

}
#endif