/**
 * @file SymmetryStatistics.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2018-03-12
 * Created on 2018-03-12.
 */

#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat
{
	class SymmetryStatistics : public Statistics
	{
	private:
		// Members.
		/**
		 * Example for a statistic.
		 */
		std::size_t mExampleStatistic = 0;
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
		SymmetryStatistics( const std::string& _statisticName ):
			Statistics( _statisticName )
		{}
		~SymmetryStatistics() {}
	};
}

#endif
