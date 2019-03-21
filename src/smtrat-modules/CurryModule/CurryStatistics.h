/**
 * @file CurryStatistics.h
 * @author Henrich Lauko <xlauko@mail.muni.cz>
 * @author Dominika Krejci <dominika.krejci@rwth-aachen.de>
 *
 * @version 2018-11-18
 * Created on 2018-11-18.
 */

#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <lib/utilities/stats/Statistics.h>

namespace smtrat
{
	class CurryStatistics : public Statistics
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
		CurryStatistics( const std::string& _statisticName ):
			Statistics( _statisticName, this ),
			mExampleStatistic( 0 )
		{}
		~CurryStatistics() {}
	};
}

#endif
