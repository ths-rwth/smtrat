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
#include "../../utilities/stats/Statistics.h"

namespace smtrat
{
	class STropStatistics : public Statistics
	{
		private:
			STropStatistics(const std::string& _statisticName)
				: Statistics(_statisticName, this)
				{}
	};
}

#endif
