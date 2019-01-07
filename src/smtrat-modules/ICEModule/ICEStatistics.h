/**
 * @file ICEStatistics.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-11-24
 * Created on 2015-11-24.
 */

#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat
{
	class ICEStatistics : public Statistics
	{
	private:
	public:
		// Override Statistics::collect.
		void collect()
		{
		}
		ICEStatistics( const std::string& _statisticName ):
			Statistics( _statisticName )
		{}
		~ICEStatistics() {}
	};
}

#endif
