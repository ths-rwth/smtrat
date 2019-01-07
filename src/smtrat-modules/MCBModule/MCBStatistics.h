/**
 * @file MCBStatistics.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-12-10
 * Created on 2015-12-10.
 */

#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat
{
	class MCBStatistics : public Statistics
	{
	private:
	public:
		// Override Statistics::collect.
		void collect()
		{
		}
		MCBStatistics( const std::string& _statisticName ):
			Statistics( _statisticName )
		{}
		~MCBStatistics() {}
	};
}

#endif
