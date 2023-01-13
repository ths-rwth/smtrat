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
				std::size_t m_accumulated_conflict_sizes = 0;
				std::size_t m_gauss_needed = false;
				std::size_t m_generated_constraints = 0;
				std::size_t m_systems = 0;
				std::size_t m_ignored_branches = 0;
				std::size_t m_total_branches = 0;
				std::size_t m_max_branches = 0;
				std::size_t m_eliminated_without_bounds = 0;
				std::size_t m_eliminated_with_bounds = 0;
				std::size_t m_total_backtrack_distance = 0;
				std::size_t m_local_conflicts_from_prune = 0;
				std::size_t m_neq_splits = 0;
				std::size_t m_unsat = 0;
				double m_avg_bound_ratio = 0;
				carl::statistics::timer m_timer;
				std::size_t m_imbert_ignored = 0;

			public:
				void global_conflict() { m_global_conflicts++; }
				void local_conflict (std::size_t distance) {
					m_local_conflicts++;
					m_total_backtrack_distance += distance;
				}
				void unsat() { m_unsat++; }
				void local_conflict_from_prune() { m_local_conflicts_from_prune++; }
				void gauss_conflict () { m_gauss_conflicts++;  }
				void conflict_size(std::size_t n) { m_accumulated_conflict_sizes += n; }
				void gauss_needed() { m_gauss_needed = true; }
				void generated_constraints(std::size_t n) { m_generated_constraints += n; }
				void imbert_ignored() { m_imbert_ignored++; }
				void new_system() { m_systems++; }
				void branches(std::size_t n) {
					m_total_branches += n;
					m_max_branches = std::max(m_max_branches, n);
				}
				void ignored_branches(std::size_t n) { m_ignored_branches += n; }
				void eliminated_without_bounds() { 
					m_eliminated_without_bounds++;
					branches(1);
				}
				void eliminated_with_bounds(std::size_t eliminators, std::size_t others) { 
					m_eliminated_with_bounds++;
					m_avg_bound_ratio = ((eliminators/static_cast<double>(others) + (m_eliminated_with_bounds - 1) * m_avg_bound_ratio)/m_eliminated_with_bounds);
				}
				void neq_splits(std::size_t n) { m_neq_splits += n; }

				auto& timer() { return m_timer; }

				void collect() { // called after the solving process to collect statistics
					Statistics::addKeyValuePair("global_conflicts", m_global_conflicts);
					Statistics::addKeyValuePair("local_conflicts", m_local_conflicts);
					Statistics::addKeyValuePair("avg_bt_distance", ((double) m_total_backtrack_distance) / ((double) m_unsat));
					Statistics::addKeyValuePair("local_conflicts_from_prune", m_local_conflicts_from_prune);
					Statistics::addKeyValuePair("avg_conflict_size", ((double) m_accumulated_conflict_sizes)/((double) m_timer.count()));
					Statistics::addKeyValuePair("gauss_conflicts", m_gauss_conflicts);
					Statistics::addKeyValuePair("gauss_needed", m_gauss_needed);
					Statistics::addKeyValuePair("generated_constraints", m_generated_constraints);
					Statistics::addKeyValuePair("imbert_ignored", m_imbert_ignored);
					Statistics::addKeyValuePair("systems", m_systems);
					Statistics::addKeyValuePair("unbounded_levels", m_eliminated_without_bounds);
					Statistics::addKeyValuePair("bounded_levels", m_eliminated_with_bounds);
					Statistics::addKeyValuePair("avg_bound_ratio", m_avg_bound_ratio);
					Statistics::addKeyValuePair("total_branches", m_total_branches);
					Statistics::addKeyValuePair("ignored_branches", m_ignored_branches);
					Statistics::addKeyValuePair("max_branches", m_max_branches);
					Statistics::addKeyValuePair("neq_splits", m_neq_splits);
					Statistics::addKeyValuePair("avg_branches", ((double) m_total_branches) / ((double) m_systems));
					Statistics::addKeyValuePair("timer", m_timer);
				}

				static FMPlexStatistics& get_instance() {
					static FMPlexStatistics& instance = statistics_get<FMPlexStatistics>("fmplex");
					return instance;
				}
		};
	} // namespace fmplex
} // namespace smtrat

#endif