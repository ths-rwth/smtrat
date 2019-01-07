/**
 * @file PBPPStatistics.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2016-11-23
 * Created on 2016-11-23.
 */

#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat
{
	class PBPPStatistics : public Statistics
	{
	private:
	public:
		// Override Statistics::collect.
		void collect()
		{
		}
		PBPPStatistics( const std::string& _statisticName ):
			Statistics( _statisticName )
		{}
		~PBPPStatistics() {}
	};
}

#endif
