/**
 * @file CoCoAGBStatistics.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2017-11-29
 * Created on 2017-11-29.
 */

#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat
{
	class CoCoAGBStatistics : public Statistics
	{
	public:
		// Override Statistics::collect.
		void collect()
		{
		}
		CoCoAGBStatistics( const std::string& _statisticName ):
			Statistics( _statisticName )
		{}
		~CoCoAGBStatistics() {}
	};
}

#endif
