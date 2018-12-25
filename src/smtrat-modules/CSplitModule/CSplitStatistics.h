/**
 * @file CSplitStatistics.h
 * @author Ömer Sali <oemer.sali@rwth-aachen.de>
 *
 * @version 2017-11-01
 * Created on 2017-11-01.
 */

#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <lib/utilities/stats/Statistics.h>

namespace smtrat
{
	class CSplitStatistics : public Statistics
	{
		public:
			CSplitStatistics( const std::string& _statisticName ):
				Statistics( _statisticName, this )
			{}
	};
}

#endif
