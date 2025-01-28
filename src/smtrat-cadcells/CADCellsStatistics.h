#pragma once

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics

#include "./common.h"
#include "datastructures/roots.h"
#include "datastructures/delineation.h"


namespace smtrat {
namespace cadcells {

using carl::operator<<;

class CADCellsStatistics : public Statistics {

public:
    enum class ProjectionType {
        resultant,
        discriminant,
        leading_coefficient,
        coefficient,
        derivative,
        factor
    };
    static std::string to_string(const ProjectionType& p) {
        switch (p) {
        case ProjectionType::resultant:
            return "resultant";
        case ProjectionType::discriminant:
            return "discriminant";
        case ProjectionType::leading_coefficient:
            return "leading_coefficient";
        case ProjectionType::coefficient:
            return "coefficient";
        case ProjectionType::derivative:
            return "derivative";
        case ProjectionType::factor:
            return "factor";
        default:
            return "x";
        }
    }

private:
    carl::statistics::MultiCounter<std::pair<std::size_t, std::size_t>> m_depth_section_common_zeros_count;
    std::size_t m_section_count = 0;

    carl::statistics::MultiCounter<std::size_t> m_interval_point_count_by_depth;
    carl::statistics::MultiCounter<std::size_t> m_interval_open_count_by_depth;
    carl::statistics::MultiCounter<std::size_t> m_interval_halfclosed_count_by_depth;
    carl::statistics::MultiCounter<std::size_t> m_interval_closed_count_by_depth;
    carl::statistics::MultiCounter<std::size_t> m_interval_unbounded_count_by_depth;
    carl::statistics::MultiCounter<std::size_t> m_interval_halfunbounded_count_by_depth;
    carl::statistics::MultiCounter<std::size_t> m_interval_count_by_depth;

    carl::statistics::MultiCounter<std::size_t> m_representation_equational_count_by_depth;
    carl::statistics::MultiCounter<std::size_t> m_representation_roots_inside_by_depth;

    carl::statistics::MultiCounter<std::size_t> m_rules_intersection_count_by_depth;

    carl::statistics::Timer m_proj_timer;

    boost::container::flat_map<ProjectionType, carl::statistics::Series> m_proj_x_total_degree;
    boost::container::flat_map<ProjectionType, carl::statistics::Series> m_proj_x_degree;
    boost::container::flat_map<ProjectionType, carl::statistics::Series> m_proj_x_level;

    carl::statistics::Series m_proj_realroots_num_roots;
    std::size_t m_proj_realroots_nullified_count = 0;

    std::size_t m_proj_realroots_count = 0;
    std::size_t m_proj_realroots_algebraic_count = 0;
    std::size_t m_proj_evaluate_count = 0;
    std::size_t m_proj_evaluate_algebraic_count = 0;

    carl::statistics::MultiCounter<std::size_t> m_filter_poly_count_by_depth;
    carl::statistics::MultiCounter<std::pair<std::size_t, std::size_t>> m_filter_poly_count_by_depth_and_num_factors;
    carl::statistics::MultiCounter<std::pair<std::size_t, std::size_t>> m_filter_poly_count_by_depth_and_num_roots;
    carl::statistics::MultiCounter<std::size_t> m_filter_poly_count_independent_by_depth;

    std::size_t m_current_max_level;

    std::size_t m_filter_current_level;
    bool m_filter_current_underlying_algebraic;
    bool m_filter_current_indep;

    bool m_filter_current_has_zeros_irred = false;
    carl::statistics::MultiCounter<std::size_t> m_filter_poly_count_has_zeros_irred_indep_by_depth;

    carl::statistics::Timer m_timer_filter_roots;
    carl::statistics::Timer m_timer_filter_roots_callback;

    carl::statistics::MultiCounter<std::size_t> m_filter_root_by_depth;
    carl::statistics::MultiCounter<std::size_t> m_filter_root_algebraic_by_depth;
    carl::statistics::MultiCounter<std::size_t> m_filter_root_sample_algebraic_by_depth;
    carl::statistics::MultiCounter<std::size_t> m_filter_root_optional_by_depth;
    carl::statistics::MultiCounter<std::size_t> m_filter_root_inclusive_by_depth;

    std::size_t m_filter_roots_got_optional_outside_delin_inter = 0;
    std::size_t m_filter_roots_got_normal_outside_delin_inter = 0;
    std::size_t m_filter_roots_check_inside_delin_inter = 0;
    std::size_t m_filter_roots_check_outside_delin_inter = 0;
    std::size_t m_filter_roots_check_pair_with_interval = 0;
    std::size_t m_filter_roots_check_pair_without_interval = 0;

    std::size_t m_filter_roots_skipped_using_sample = 0;

public:
    carl::statistics::Timer m_proj_timer_is_zero;
    carl::statistics::Timer m_proj_timer_num_roots;
    carl::statistics::Timer m_proj_timer_real_roots;
    carl::statistics::Timer m_proj_timer_is_nullified;
    carl::statistics::Timer m_proj_timer_resultant;
    carl::statistics::Timer m_proj_timer_discriminant;
    carl::statistics::Timer m_proj_timer_ldcf;
    carl::statistics::Timer m_proj_timer_factors_nonconst;
    carl::statistics::Timer m_proj_timer_coeffs;
    carl::statistics::Timer m_proj_timer_simplest_nonzero_coeff;
    carl::statistics::Timer m_proj_timer_derivative;

    bool enabled() const {
        return true;
    }

    void collect() {
        Statistics::addKeyValuePair("heuristics.section.common_zeros_count.by_depth", m_depth_section_common_zeros_count);
        Statistics::addKeyValuePair("heuristics.section.count", m_section_count);

        Statistics::addKeyValuePair("heuristics.interval.point_count.by_depth", m_interval_point_count_by_depth);
        Statistics::addKeyValuePair("heuristics.interval.open_count.by_depth", m_interval_open_count_by_depth);
        Statistics::addKeyValuePair("heuristics.interval.halfclosed_count.by_depth", m_interval_halfclosed_count_by_depth);
        Statistics::addKeyValuePair("heuristics.interval.closed_count.by_depth", m_interval_closed_count_by_depth);
        Statistics::addKeyValuePair("heuristics.interval.unbounded_count.by_depth", m_interval_unbounded_count_by_depth);
        Statistics::addKeyValuePair("heuristics.interval.halfunbounded_count.by_depth", m_interval_halfunbounded_count_by_depth);
        Statistics::addKeyValuePair("heuristics.interval.count.by_depth", m_interval_count_by_depth);

        Statistics::addKeyValuePair("heuristics.representation.equational_count.by_depth", m_representation_equational_count_by_depth);
        Statistics::addKeyValuePair("heuristics.representation.roots_inside.by_depth", m_representation_roots_inside_by_depth);

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
        Statistics::addKeyValuePair("projections.real_roots.count", m_proj_realroots_count);
        Statistics::addKeyValuePair("projections.real_roots.algebraic.count", m_proj_realroots_algebraic_count);

        Statistics::addKeyValuePair("projections.evaluate.count", m_proj_evaluate_count);
        Statistics::addKeyValuePair("projections.evaluate.algebraic.count", m_proj_evaluate_algebraic_count);

        Statistics::addKeyValuePair("projections.timer", m_proj_timer);
        Statistics::addKeyValuePair("projections.timer.is_zero", m_proj_timer_is_zero);
        Statistics::addKeyValuePair("projections.timer.num_roots", m_proj_timer_num_roots);
        Statistics::addKeyValuePair("projections.timer.real_roots", m_proj_timer_real_roots);
        Statistics::addKeyValuePair("projections.timer.is_nullified", m_proj_timer_is_nullified);
        Statistics::addKeyValuePair("projections.timer.resultant", m_proj_timer_resultant);
        Statistics::addKeyValuePair("projections.timer.discriminant", m_proj_timer_discriminant);
        Statistics::addKeyValuePair("projections.timer.ldcf", m_proj_timer_ldcf);
        Statistics::addKeyValuePair("projections.timer.factors_nonconst", m_proj_timer_factors_nonconst);
        Statistics::addKeyValuePair("projections.timer.coeffs", m_proj_timer_coeffs);
        Statistics::addKeyValuePair("projections.timer.simplest_nonzero_coeff", m_proj_timer_simplest_nonzero_coeff);
        Statistics::addKeyValuePair("projections.timer.derivative", m_proj_timer_derivative);

        Statistics::addKeyValuePair("filter.poly_count.by_depth", m_filter_poly_count_by_depth);
        Statistics::addKeyValuePair("filter.poly_count.by_depth_and_num_factors", m_filter_poly_count_by_depth_and_num_factors);
        Statistics::addKeyValuePair("filter.poly_count.by_depth_and_num_roots", m_filter_poly_count_by_depth_and_num_roots);
        Statistics::addKeyValuePair("filter.poly_count.independent.by_depth", m_filter_poly_count_independent_by_depth);
        Statistics::addKeyValuePair("filter.poly_count.has_zeros_irred_indep.by_depth", m_filter_poly_count_has_zeros_irred_indep_by_depth);

        Statistics::addKeyValuePair("filter.timer.filter_roots", m_timer_filter_roots);
        Statistics::addKeyValuePair("filter.timer.filter_roots_callback", m_timer_filter_roots_callback);

        Statistics::addKeyValuePair("filter.root.by_depth", m_filter_root_by_depth);
        Statistics::addKeyValuePair("filter.root.algebraic.by_depth", m_filter_root_algebraic_by_depth);
        Statistics::addKeyValuePair("filter.root.sample_algebraic.by_depth", m_filter_root_sample_algebraic_by_depth);
        Statistics::addKeyValuePair("filter.root.optional.by_depth", m_filter_root_optional_by_depth);
        Statistics::addKeyValuePair("filter.root.inclusive.by_depth", m_filter_root_inclusive_by_depth);

        Statistics::addKeyValuePair("filter.root.optional_outside_delin_inter", m_filter_roots_got_optional_outside_delin_inter);
        Statistics::addKeyValuePair("filter.root.normal_outside_delin_inter", m_filter_roots_got_normal_outside_delin_inter);
        Statistics::addKeyValuePair("filter.root.check_inside_delin_inter", m_filter_roots_check_inside_delin_inter);
        Statistics::addKeyValuePair("filter.root.check_outside_delin_inter", m_filter_roots_check_outside_delin_inter);
        Statistics::addKeyValuePair("filter.root.check_pair_with_interval", m_filter_roots_check_pair_with_interval);
        Statistics::addKeyValuePair("filter.root.check_pair_without_interval", m_filter_roots_check_pair_without_interval);
        Statistics::addKeyValuePair("filter.root.skipped_using_sample", m_filter_roots_skipped_using_sample);
    }

    // projections

    void projection_start() {
        m_proj_timer.start_this();
    }
    void projection_end() {
        m_proj_timer.finish();
    }

    void projection_poly(const ProjectionType& type, std::size_t total_degree, std::size_t degree, std::size_t level) {
        m_proj_x_total_degree.try_emplace(type).first->second.add(total_degree);
        m_proj_x_degree.try_emplace(type).first->second.add(degree);
        m_proj_x_level.try_emplace(type).first->second.add(level);
    }
    void resultant(std::size_t total_degree, std::size_t degree, std::size_t level) {
        projection_poly(ProjectionType::resultant, total_degree, degree, level);
    }
    void discriminant(std::size_t total_degree, std::size_t degree, std::size_t level) {
        projection_poly(ProjectionType::discriminant, total_degree, degree, level);
    }
    void leading_coefficient(std::size_t total_degree, std::size_t degree, std::size_t level) {
        projection_poly(ProjectionType::leading_coefficient, total_degree, degree, level);
    }
    void coefficient(std::size_t total_degree, std::size_t degree, std::size_t level) {
        projection_poly(ProjectionType::coefficient, total_degree, degree, level);
    }
    void derivative(std::size_t total_degree, std::size_t degree, std::size_t level) {
        projection_poly(ProjectionType::derivative, total_degree, degree, level);
    }
    void factor(std::size_t total_degree, std::size_t degree, std::size_t level) {
        projection_poly(ProjectionType::factor, total_degree, degree, level);
    }

    void real_roots_result(const carl::RealRootsResult<RAN>& result) {
        if (result.is_nullified()) {
            m_proj_realroots_nullified_count++;
        }
        m_proj_realroots_num_roots.add(result.is_nullified() ? 0 : result.roots().size());
    }

    void evaluate_call(const cadcells::Assignment& ass) {
        bool algebraic = std::find_if(ass.begin(), ass.end(), [](const auto& m) { return !m.second.is_numeric(); }) != ass.end();
        m_proj_evaluate_count++;
        if (algebraic) m_proj_evaluate_algebraic_count++;
    }

    void real_roots_call(const cadcells::Assignment& ass) {
        bool algebraic = std::find_if(ass.begin(), ass.end(), [](const auto& m) { return !m.second.is_numeric(); }) != ass.end();
        m_proj_realroots_count++;
        if (algebraic) m_proj_realroots_algebraic_count++;
    }

    // misc

    void set_max_level(std::size_t level) {
        m_current_max_level = level;
    }

    // filter_roots

    void filter_roots_start(std::size_t level, std::size_t num_factors, std::size_t num_roots, const cadcells::Assignment& ass) {
        assert(m_current_max_level >= level);
        m_filter_poly_count_by_depth.inc(m_current_max_level - level, 1);
        m_filter_poly_count_by_depth_and_num_factors.inc(std::make_pair((std::size_t)m_current_max_level - level, num_factors), 1);
        m_filter_poly_count_by_depth_and_num_roots.inc(std::make_pair((std::size_t)m_current_max_level - level, num_roots), 1);

        m_filter_current_has_zeros_irred = num_factors == 1 && num_roots > 0;

        m_filter_current_level = level;
        m_filter_current_underlying_algebraic = std::find_if(ass.begin(), ass.end(), [](const auto& m) { return !m.second.is_numeric(); }) != ass.end();
        m_filter_current_indep = true;

        m_timer_filter_roots.start_this();
    }
    void filter_roots_end() {
        if (m_filter_current_indep) {
            m_filter_poly_count_independent_by_depth.inc(m_current_max_level-m_filter_current_level, 1);
            if (m_filter_current_has_zeros_irred) {
                m_filter_poly_count_has_zeros_irred_indep_by_depth.inc(m_current_max_level-m_filter_current_level, 1);
            }
        }

        m_timer_filter_roots.finish();
    }
    void filter_roots_filter_start(const cadcells::RAN& ran) {
        m_filter_root_by_depth.inc(m_current_max_level - m_filter_current_level, 1);
        if (!ran.is_numeric()) {
            m_filter_root_algebraic_by_depth.inc(m_current_max_level - m_filter_current_level, 1);
        }
        if (m_filter_current_underlying_algebraic || !ran.is_numeric()) {
            m_filter_root_sample_algebraic_by_depth.inc(m_current_max_level - m_filter_current_level, 1);
        }

        m_timer_filter_roots_callback.start_this();
    }
    void filter_roots_filter_end() {
        m_timer_filter_roots_callback.finish();
    }

    void filter_roots_got_normal(const cadcells::RAN&) {
        m_filter_current_indep = false;
    }
    void filter_roots_got_inclusive(const cadcells::RAN&) {
        m_filter_root_inclusive_by_depth.inc(m_current_max_level - m_filter_current_level, 1);
        m_filter_current_indep = false;
    }
    void filter_roots_got_optional(const cadcells::RAN&) {
        m_filter_root_optional_by_depth.inc(m_current_max_level - m_filter_current_level, 1);
    }
    void filter_roots_got_inclusive_optional(const cadcells::RAN&) {
        m_filter_root_optional_by_depth.inc(m_current_max_level - m_filter_current_level, 1);
        m_filter_root_inclusive_by_depth.inc(m_current_max_level - m_filter_current_level, 1);
    }

    void filter_roots_got_optional_outside_delin_inter() {
        m_filter_roots_got_optional_outside_delin_inter++;
    }
    void filter_roots_got_normal_outside_delin_inter() {
        m_filter_roots_got_normal_outside_delin_inter++;
    }
    void filter_roots_check_inside_delin_inter() {
        m_filter_roots_check_inside_delin_inter++;
    }
    void filter_roots_check_outside_delin_inter() {
        m_filter_roots_check_outside_delin_inter++;
    }

    void filter_roots_check_pair_with_interval() {
        m_filter_roots_check_pair_with_interval++;
    }
    void filter_roots_check_pair_without_interval() {
        m_filter_roots_check_pair_without_interval++;
    }

    void filter_roots_skipped_using_sample() {
        m_filter_roots_skipped_using_sample++;
    }
 
    // heuristics

    void section_common_zeros(std::size_t level, std::size_t num_common_eq_constr) {
        m_depth_section_common_zeros_count.inc(std::make_pair(m_current_max_level-level,num_common_eq_constr), 1);
        m_section_count++;
    }

    void got_bound(std::size_t level, const datastructures::SymbolicInterval& interval) {
        m_interval_count_by_depth.inc(m_current_max_level-level, 1);

        if (interval.is_section()) {
            m_interval_point_count_by_depth.inc(m_current_max_level-level, 1);
        } else {
            if(interval.lower().is_infty() && interval.upper().is_infty()) {
                m_interval_unbounded_count_by_depth.inc(m_current_max_level-level, 1);
            } else if (interval.lower().is_infty() || interval.upper().is_infty()) {
                m_interval_halfunbounded_count_by_depth.inc(m_current_max_level-level, 1);
            }        

            if(interval.lower().is_weak() && interval.upper().is_weak()) {
                m_interval_closed_count_by_depth.inc(m_current_max_level-level, 1);
            } else if(interval.lower().is_strict() && interval.upper().is_strict()) {
                m_interval_open_count_by_depth.inc(m_current_max_level-level, 1);
            } else if (interval.lower().is_weak() || interval.upper().is_weak()) {
                m_interval_halfclosed_count_by_depth.inc(m_current_max_level-level, 1);
            }
        }
    }

    void got_representation_equational(std::size_t level, std::size_t num) {
        m_representation_equational_count_by_depth.inc(m_current_max_level-level, num);
    }

    void got_representation_roots_inside(std::size_t level, const datastructures::Delineation& delin, const datastructures::DelineationInterval& interval) {
        if (interval.is_section()) {
            m_representation_roots_inside_by_depth.inc(m_current_max_level-level, 0);
        } else if (interval.lower_unbounded() && interval.upper_unbounded()) {
            m_representation_roots_inside_by_depth.inc(m_current_max_level-level, delin.roots().size());
        } else if (interval.lower_unbounded()) {
            m_representation_roots_inside_by_depth.inc(m_current_max_level-level, std::distance(delin.roots().begin(), interval.upper()));
        } else if (interval.upper_unbounded()) {
            m_representation_roots_inside_by_depth.inc(m_current_max_level-level, std::distance(interval.lower(), delin.roots().end())-1);
        } else {
            m_representation_roots_inside_by_depth.inc(m_current_max_level-level, std::distance(interval.lower(), interval.upper())-1);
        }
    }

    /// rules

    void detect_intersection(std::size_t level) {
        m_rules_intersection_count_by_depth.inc(m_current_max_level-level, 1);
    }
};

CADCellsStatistics& statistics();

} // namespace cadcells
} // namespace smtrat

#endif
