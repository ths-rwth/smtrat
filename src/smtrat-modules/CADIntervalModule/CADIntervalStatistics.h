/**
 * @file CADIntervalStatistics.h
 * @author Hanna Franzen <hanna.franzen@rwth-aachen.de>
 *
 * @version 2019-02-20
 * Created on 2019-02-20.
 */

#pragma once

#ifdef SMTRAT_DEVOPTION_Statistics
#include <lib/utilities/stats/Statistics.h>

namespace smtrat
{
	class CADIntervalStatistics : public Statistics
	{
	private:
		// Members.
		/**
		 * Example for a statistic.
		 */
		size_t mExampleStatistic;
	public:
		// Override Statistics::collect.
		void collect()
		{
		   Statistics::addKeyValuePair( "example_statistic", mExampleStatistic );
		}
		void foo()
		{
			++mExampleStatistic;
		}
		CADIntervalStatistics( const std::string& _statisticName ):
			Statistics( _statisticName, this ),
			mExampleStatistic( 0 )
		{}
		~CADIntervalStatistics() {}
	};
}

#endif
