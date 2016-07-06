/**
 * @file NewCADStatistics.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2016-02-23
 * Created on 2016-02-23.
 */

#pragma once

#include "../../config.h"
#ifdef SMTRAT_DEVOPTION_Statistics
#include "../../utilities/stats/Statistics.h"

namespace smtrat
{
	class NewCADStatistics : public Statistics {
	private:
		std::size_t mMaxProjectionSize = 0;
	public:
		void collect()
		{
		   Statistics::addKeyValuePair("max_projection_size", mMaxProjectionSize);
		}
		void currentProjectionSize(std::size_t size) {
			mMaxProjectionSize = std::max(mMaxProjectionSize, size);
		}
		NewCADStatistics( const std::string& _statisticName ):
			Statistics( _statisticName, this )
		{}
		~NewCADStatistics() {}
	};
}

#endif
