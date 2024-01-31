#pragma once

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics

#include "./common.h"
#include <carl-arith/ran/common/RealRoots.h>
#include "datastructures/roots.h"


namespace smtrat {
namespace cadcells {

using carl::operator<<;

class CADCellsStatistics : public Statistics {

public:
    enum class ProjectionType {
        resultant, discriminant, leading_coefficient, coefficient, derivative, factor
    };
    static std::string to_string(const ProjectionType& p) {
        switch(p) {
            case ProjectionType::resultant: return "resultant";
            case ProjectionType::discriminant: return "discriminant";
            case ProjectionType::leading_coefficient: return "leading_coefficient";
            case ProjectionType::coefficient: return "coefficient";
            case ProjectionType::derivative: return "derivative";
            case ProjectionType::factor: return "factor";
            default: return "x";
        }
    }

private:
    carl::statistics::MultiCounter<std::pair<std::size_t, std::size_t>> m_depth_section_common_zeros_count;

    carl::statistics::MultiCounter<std::size_t> m_interval_point_count_by_depth;
    carl::statistics::MultiCounter<std::size_t> m_interval_open_count_by_depth;
    carl::statistics::MultiCounter<std::size_t> m_interval_halfopen_count_by_depth;
    carl::statistics::MultiCounter<std::size_t> m_interval_closed_count_by_depth;
    carl::statistics::MultiCounter<std::size_t> m_interval_unbounded_count_by_depth;
    carl::statistics::MultiCounter<std::size_t> m_interval_halfunbounded_count_by_depth;

    carl::statistics::MultiCounter<std::size_t> m_representation_equational_count_by_depth;

    carl::statistics::MultiCounter<std::size_t> m_rules_intersection_count_by_depth;

    boost::container::flat_map<ProjectionType, carl::statistics::Series> m_proj_x_total_degree;
    boost::container::flat_map<ProjectionType, carl::statistics::Series> m_proj_x_degree;
    boost::container::flat_map<ProjectionType, carl::statistics::Series> m_proj_x_level;

    carl::statistics::Series m_proj_realroots_num_roots;
    std::size_t m_proj_realroots_nullified_count;

    carl::statistics::MultiCounter<std::size_t> m_filter_poly_count_by_depth;
    carl::statistics::MultiCounter<std::pair<std::size_t, std::size_t>> m_filter_poly_count_by_depth_and_num_factors;
    carl::statistics::MultiCounter<std::pair<std::size_t, std::size_t>> m_filter_poly_count_by_depth_and_num_roots;
    carl::statistics::MultiCounter<std::size_t> m_filter_poly_count_independent_by_depth;

    std::size_t m_current_max_level;

    std::size_t m_filter_current_level;
    bool m_filter_current_underlying_algebraic;
    bool m_filter_current_indep;

    carl::statistics::Timer m_timer_filter_roots;
    carl::statistics::Timer m_timer_filter_roots_callback;

    carl::statistics::MultiCounter<std::size_t> m_filter_root_by_depth;
    carl::statistics::MultiCounter<std::size_t> m_filter_root_algebraic_by_depth;
    carl::statistics::MultiCounter<std::size_t> m_filter_root_sample_algebraic_by_depth;
    carl::statistics::MultiCounter<std::size_t> m_filter_root_optional_by_depth;
    carl::statistics::MultiCounter<std::size_t> m_filter_root_inclusive_by_depth;

public:
    bool enabled() const {
        return true;
    }

    void collect() {
        Statistics::addKeyValuePair("heuristics.section.common_zeros_count.by_depth", m_depth_section_common_zeros_count);

        Statistics::addKeyValuePair("heuristics.interval.point_count.by_depth", m_interval_point_count_by_depth);
        Statistics::addKeyValuePair("heuristics.interval.open_count.by_depth", m_interval_open_count_by_depth);
        Statistics::addKeyValuePair("heuristics.interval.halfopen_count.by_depth", m_interval_halfopen_count_by_depth);
        Statistics::addKeyValuePair("heuristics.interval.closed_count.by_depth", m_interval_closed_count_by_depth);
        Statistics::addKeyValuePair("heuristics.interval.unbounded_count.by_depth", m_interval_unbounded_count_by_depth);
        Statistics::addKeyValuePair("heuristics.interval.halfunbounded_count.by_depth", m_interval_halfunbounded_count_by_depth);

        Statistics::addKeyValuePair("heuristics.representation.equational_count.by_depth", m_representation_equational_count_by_depth);

        Statistics::addKeyValuePair("heuristics.rules.intersection_count.by_depth", m_rules_intersection_count_by_depth);

        for (const auto& [k, v] : m_proj_x_total_degree) {
            Statistics::addKeyValuePair("projections." + to_string(k) + ".total_degree", v);
        }
        for (const auto& [k, v] : m_proj_x_degree) {
            Statistics::addKeyValuePair("projections." + to_string(k) + ".degree", v);
        }
        for (const auto& [k, v] : m_proj_x_level) {
            Statistics::addKeyValuePair("projections." + to_string(k) + ".level", v);
        }

        Statistics::addKeyValuePair("projections.real_roots.num_roots", m_proj_realroots_num_roots);
        Statistics::addKeyValuePair("projections.real_roots.nullified.count", m_proj_realroots_nullified_count);

        Statistics::addKeyValuePair("filter.poly_count.by_depth", m_filter_poly_count_by_depth);
        Statistics::addKeyValuePair("filter.poly_count.by_depth_and_num_factors", m_filter_poly_count_by_depth_and_num_factors);
        Statistics::addKeyValuePair("filter.poly_count.by_depth_and_num_roots", m_filter_poly_count_by_depth_and_num_roots);
        Statistics::addKeyValuePair("filter.poly_count.independent.by_depth", m_filter_poly_count_independent_by_depth);

        Statistics::addKeyValuePair("filter.timer.filter_roots", m_timer_filter_roots);
        Statistics::addKeyValuePair("filter.timer.filter_roots_callback", m_timer_filter_roots_callback);


        Statistics::addKeyValuePair("filter.root.by_depth", m_filter_root_by_depth);
        Statistics::addKeyValuePair("filter.root.algebraic.by_depth", m_filter_root_algebraic_by_depth);
        Statistics::addKeyValuePair("filter.root.sample_algebraic.by_depth", m_filter_root_sample_algebraic_by_depth);
        Statistics::addKeyValuePair("filter.root.optional.by_depth", m_filter_root_optional_by_depth);
        Statistics::addKeyValuePair("filter.root.inclusive.by_depth", m_filter_root_inclusive_by_depth);
    }


    // projections

    void projection_poly(const ProjectionType& type, std::size_t total_degree, std::size_t degree, std::size_t level) {
        m_proj_x_total_degree.try_emplace(type).first->second.add(total_degree);
        m_proj_x_degree.try_emplace(type).first->second.add(degree);
        m_proj_x_level.try_emplace(type).first->second.add(level);
    }
    void resultant          (std::size_t total_degree, std::size_t degree, std::size_t level) { projection_poly(ProjectionType::resultant          , total_degree, degree, level); }
    void discriminant       (std::size_t total_degree, std::size_t degree, std::size_t level) { projection_poly(ProjectionType::discriminant       , total_degree, degree, level); }
    void leading_coefficient(std::size_t total_degree, std::size_t degree, std::size_t level) { projection_poly(ProjectionType::leading_coefficient, total_degree, degree, level); }
    void coefficient        (std::size_t total_degree, std::size_t degree, std::size_t level) { projection_poly(ProjectionType::coefficient        , total_degree, degree, level); }
    void derivative         (std::size_t total_degree, std::size_t degree, std::size_t level) { projection_poly(ProjectionType::derivative         , total_degree, degree, level); }
    void factor             (std::size_t total_degree, std::size_t degree, std::size_t level) { projection_poly(ProjectionType::factor             , total_degree, degree, level); }

    void real_roots_result(const carl::RealRootsResult<RAN>& result) {
        if (result.is_nullified()) {
            m_proj_realroots_nullified_count++;
        }
        m_proj_realroots_num_roots.add(result.is_nullified() ? 0 : result.roots().size());
    }


    // filter_roots

    void set_max_level(std::size_t level) {
        m_current_max_level = level;
    }
    void filter_roots_start(std::size_t level, std::size_t num_factors, std::size_t num_roots, const cadcells::Assignment& ass) {
        assert(m_current_max_level>=level);
        m_filter_poly_count_by_depth.inc(m_current_max_level-level, 1);
        m_filter_poly_count_by_depth_and_num_factors.inc(std::make_pair((std::size_t)m_current_max_level-level, num_factors), 1);
        m_filter_poly_count_by_depth_and_num_roots.inc(std::make_pair((std::size_t)m_current_max_level-level, num_roots), 1);

        m_filter_current_level = level;
        m_filter_current_underlying_algebraic = std::find_if(ass.begin(), ass.end(), [](const auto& m) { return !m.second.is_numeric(); }) != ass.end();
        m_filter_current_indep = true;

        m_timer_filter_roots.start_this();
    }
    void filter_roots_end() {
        if (m_filter_current_indep) {
            m_filter_poly_count_independent_by_depth.inc(m_current_max_level-m_filter_current_level, 1);
        }

        m_timer_filter_roots.finish();
    }
    void filter_roots_filter_start(const cadcells::RAN& ran) {
        m_filter_root_by_depth.inc(m_current_max_level-m_filter_current_level, 1);
        if (!ran.is_numeric()) {
            m_filter_root_algebraic_by_depth.inc(m_current_max_level-m_filter_current_level, 1);
        }
        if (m_filter_current_underlying_algebraic || !ran.is_numeric()) {
            m_filter_root_sample_algebraic_by_depth.inc(m_current_max_level-m_filter_current_level, 1);
        }

        m_timer_filter_roots_callback.start_this();
    }
    void filter_roots_filter_end() {
        m_timer_filter_roots.finish();
    }

    void filter_roots_got_normal(const cadcells::RAN&) {
        m_filter_current_indep = false;
    }
    void filter_roots_got_inclusive(const cadcells::RAN&) {
        m_filter_root_inclusive_by_depth.inc(m_current_max_level-m_filter_current_level, 1);
        m_filter_current_indep = false;
    }
    void filter_roots_got_optional(const cadcells::RAN&) {
        m_filter_root_optional_by_depth.inc(m_current_max_level-m_filter_current_level, 1);
    }
    void filter_roots_got_inclusive_optional(const cadcells::RAN&) {
        m_filter_root_optional_by_depth.inc(m_current_max_level-m_filter_current_level, 1);
        m_filter_root_inclusive_by_depth.inc(m_current_max_level-m_filter_current_level, 1);
    }
    

    // heuristics

    void section_common_zeros(std::size_t depth, std::size_t num_common_eq_constr) {
        m_depth_section_common_zeros_count.inc(std::make_pair(depth,num_common_eq_constr), 1);
    }

    void got_bound(const datastructures::SymbolicInterval& interval) {
        if (interval.is_section()) {
            m_interval_point_count_by_depth.inc(m_current_max_level-m_filter_current_level, 1);
        }
        if(interval.lower().is_infty() && interval.upper().is_infty()) {
            m_interval_unbounded_count_by_depth.inc(m_current_max_level-m_filter_current_level, 1);
        } else if (interval.lower().is_infty() || interval.upper().is_infty()) {
            m_interval_halfunbounded_count_by_depth.inc(m_current_max_level-m_filter_current_level, 1);
        }        
        if(interval.lower().is_weak() && interval.upper().is_weak()) {
            m_interval_closed_count_by_depth.inc(m_current_max_level-m_filter_current_level, 1);
        } else if(interval.lower().is_strict() && interval.upper().is_strict()) {
            m_interval_open_count_by_depth.inc(m_current_max_level-m_filter_current_level, 1);
        } else {
            m_interval_halfopen_count_by_depth.inc(m_current_max_level-m_filter_current_level, 1);
        }
    }

    void got_representation_equational(std::size_t num) {
        m_representation_equational_count_by_depth.inc(m_current_max_level-m_filter_current_level, num);
    }


    /// rules

    void detect_intersection() {
        m_rules_intersection_count_by_depth.inc(m_current_max_level-m_filter_current_level, 1);
    }
};

CADCellsStatistics &statistics();

}
}

#endif
