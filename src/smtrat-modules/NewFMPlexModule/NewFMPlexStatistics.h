#pragma once

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat {
	namespace fmplex {

		class FMPlexStatistics : public Statistics {
			private:
				std::size_t m_global_conflicts = 0;
				std::size_t m_local_conflicts = 0;
				std::size_t m_gauss_conflicts = 0;
				std::size_t m_gauss_needed = false;
				std::size_t m_generated_constraints = 0;
				std::size_t m_systems = 0;
				std::size_t m_ignored_branches = 0;
				std::size_t m_total_branches = 0;
				std::size_t m_max_branches = 0;

			public:
				void global_conflict() { m_global_conflicts++; }
				void local_conflict () { m_local_conflicts++;  }
				void gauss_conflict () { m_gauss_conflicts++;  }
				void gauss_needed() { m_gauss_needed = true; }
				void generated_constraints(std::size_t n) { m_generated_constraints += n; }
				void new_system() { m_systems++; }
				void branches(std::size_t n) {
					m_total_branches += n;
					m_max_branches = std::max(m_max_branches, n);
				}
				void ignored_branches(std::size_t n) { m_ignored_branches += n; }

				void collect() { // called after the solving process to collect statistics
					Statistics::addKeyValuePair("global_conflicts", m_global_conflicts);
					Statistics::addKeyValuePair("local_conflicts", m_local_conflicts);
					Statistics::addKeyValuePair("generated_cnstraints", m_generated_constraints);
					Statistics::addKeyValuePair("systems", m_systems);
					Statistics::addKeyValuePair("total_branches", m_total_branches);
					Statistics::addKeyValuePair("ignored_branches", m_ignored_branches);
					Statistics::addKeyValuePair("max_branches", m_max_branches);
					Statistics::addKeyValuePair("avg_branches", ((double) m_total_branches) / ((double) m_systems));
				}

				static FMPlexStatistics& get_instance() {
					static FMPlexStatistics& instance = statistics_get<NewFMPlexStatistics>("fmplex");
					return instance;
				}
		};
	} // namespace fmplex
} // namespace smtrat

#endif