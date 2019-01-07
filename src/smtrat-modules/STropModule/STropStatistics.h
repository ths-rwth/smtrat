/**
 * @file STropStatistics.h
 * @author Ömer Sali <oemer.sali@rwth-aachen.de>
 *
 * @version 2018-04-04
 * Created on 2017-09-13.
 */

#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat
{
	class STropStatistics : public Statistics
	{
		public:
			STropStatistics(const std::string& _statisticName)
				: Statistics(_statisticName)
				{}
	};
}

#endif
