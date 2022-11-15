#pragma once

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat {
	namespace fmplex {

		class FMPlexStatistics : public Statistics {
			private:
				std::size_t m_global_conflicts = 0;
				std::size_t m_local_conflicts = 0;
				std::size_t m_generated_constraints = 0;

			public:
				void collect() { // called after the solving process to collect statistics
					Statistics::addKeyValuePair("gConflicts", mGlobalConflicts);
					Statistics::addKeyValuePair("lConflicts", mLocalConflicts);
					Statistics::addKeyValuePair("tConflicts", mGlobalConflicts + mLocalConflicts);
					Statistics::addKeyValuePair("generatedConstraints", mGeneratedConstraints);
				}
		};
	} // namespace fmplex
} // namespace smtrat

#endif