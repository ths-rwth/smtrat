/**
 * @file GBPPStatistics.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2018-03-09
 * Created on 2018-03-09.
 */

#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat
{
	class GBPPStatistics : public Statistics
	{
	private:
	public:
		// Override Statistics::collect.
		void collect()
		{
		}
		GBPPStatistics( const std::string& _statisticName ):
			Statistics( _statisticName )
		{}
		~GBPPStatistics() {}
	};
}

#endif
