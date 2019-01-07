/**
 * @file PBGaussStatistics.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2017-05-03
 * Created on 2017-05-03.
 */

#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat
{
	class PBGaussStatistics : public Statistics
	{
	public:
		// Override Statistics::collect.
		void collect()
		{
		}
		PBGaussStatistics( const std::string& _statisticName ):
			Statistics( _statisticName )
		{}
		~PBGaussStatistics() {}
	};
}

#endif
