#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat
{
	class LVEStatistics : public Statistics {
	public:
		std::size_t lone_variables = 0;
		std::size_t eliminated = 0;

		std::size_t elim_linear = 0;
		std::size_t elim_factors = 0;

		void collect() {
			Statistics::addKeyValuePair("lone_variables", lone_variables);
			Statistics::addKeyValuePair("eliminated", eliminated);
			Statistics::addKeyValuePair("elim_linear", elim_linear);
			Statistics::addKeyValuePair("elim_factors", elim_factors);
		}
	};
}

#endif
