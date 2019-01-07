/**
 * @file CubeLIAStatistics.h
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
	class CubeLIAStatistics : public Statistics
	{
	public:
		// Override Statistics::collect.
		void collect()
		{
		}
		CubeLIAStatistics( const std::string& _statisticName ):
			Statistics( _statisticName )
		{}
		~CubeLIAStatistics() {}
	};
}

#endif
