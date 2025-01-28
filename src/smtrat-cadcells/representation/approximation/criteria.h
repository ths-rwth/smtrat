#pragma once

#include <smtrat-cadcells/OCApproximationStatistics.h>

namespace smtrat::cadcells::representation::approximation {

using IR = datastructures::IndexedRoot;

template<typename Settings>
class ApxCriteria {
private:

    struct DynamicSettings {
        std::size_t considered_cells_limit;
        std::size_t approximated_cells_limit;
        std::size_t apx_per_constraint_limit;
        std::size_t apx_per_poly_limit;
        std::size_t single_degree_threshold;
        std::size_t pair_degree_threshold;

        bool crit_level_enabled;
        bool crit_considered_enabled;
        bool crit_apx_cells_enabled;
        bool crit_single_degree_enabled;
        bool crit_pair_degree_enabled;
        bool crit_apx_per_constraint_enabled;
        bool crit_apx_per_poly_enabled;
        bool crit_side_enabled;

        DynamicSettings() {
            considered_cells_limit   = settings_module().get("considered_cells_limit", Settings::considered_cells_limit);
            approximated_cells_limit = settings_module().get("approximated_cells_limit", Settings::approximated_cells_limit);
            apx_per_constraint_limit = settings_module().get("apx_per_constraint_limit", Settings::apx_per_constraint_limit);
            apx_per_poly_limit       = settings_module().get("apx_per_poly_limit", Settings::apx_per_poly_limit);
            single_degree_threshold  = settings_module().get("single_degree_threshold", Settings::single_degree_threshold);
            pair_degree_threshold    = settings_module().get("pair_degree_threshold", Settings::pair_degree_threshold);

            crit_level_enabled              = settings_module().get("crit_level_enabled", Settings::crit_level_enabled);
            crit_considered_enabled         = settings_module().get("crit_considered_enabled", Settings::crit_considered_enabled);
            crit_apx_cells_enabled          = settings_module().get("crit_apx_cells_enabled", Settings::crit_apx_cells_enabled);
            crit_single_degree_enabled      = settings_module().get("crit_single_degree_enabled", Settings::crit_single_degree_enabled);
            crit_pair_degree_enabled        = settings_module().get("crit_pair_degree_enabled", Settings::crit_pair_degree_enabled);
            crit_apx_per_constraint_enabled = settings_module().get("crit_apx_per_constraint_enabled", Settings::crit_apx_per_constraint_enabled);
            crit_apx_per_poly_enabled       = settings_module().get("crit_apx_per_poly_enabled", Settings::crit_apx_per_poly_enabled);
            crit_side_enabled               = settings_module().get("crit_side_enabled", Settings::crit_side_enabled);
        }
    };


    DynamicSettings m_settings = DynamicSettings();

    std::size_t m_considered_cells   = 0;
    std::size_t m_approximated_cells = 0;
    bool m_currently_approximating = false;

    std::unordered_map<Atom, std::size_t> m_constraint_involved_counter;
    std::map<std::pair<Polynomial,  std::size_t>, std::size_t> m_poly_apx_counter;
    std::vector<Atom> m_curr_constraints;


    bool crit_considered_count() {
        if (!m_settings.crit_considered_enabled) return true;
        if (m_considered_cells < m_settings.considered_cells_limit) return true;
        SMTRAT_STATISTICS_CALL(OCApproximationStatistics::get_instance().hit_considered_limit());
        return false; 
    }

    bool crit_apx_count() {
        if (!m_settings.crit_apx_cells_enabled) return true;
        if (m_approximated_cells < m_settings.approximated_cells_limit) return true;
        SMTRAT_STATISTICS_CALL(OCApproximationStatistics::get_instance().hit_approximation_limit());
        return false; 
    }

    bool crit_single_degree(datastructures::Projections& proj, const IR& ir) {
        if (!m_settings.crit_single_degree_enabled) return true;
        return proj.degree(ir.poly) >= m_settings.single_degree_threshold;
    }

    bool crit_pair_degree(datastructures::Projections& proj, const IR& ir_l, const IR& ir_u) {
        if (!m_settings.crit_pair_degree_enabled) return true;
        std::size_t deg_l = proj.degree(ir_l.poly);
        if (deg_l <= 2) return false; // TODO: magic number
        std::size_t deg_u = proj.degree(ir_u.poly);
        if (deg_u <= 2) return false;
        return deg_l * deg_u >= m_settings.pair_degree_threshold;
    }

    bool crit_poly_apx_count(datastructures::Projections& proj, const IR& ir) {
        if (!m_settings.crit_apx_per_poly_enabled) return true;
        auto p = std::make_pair(proj.polys()(ir.poly), ir.index);
        if (m_poly_apx_counter[p] < m_settings.apx_per_poly_limit) return true;
        #ifdef SMTRAT_DEVOPTION_Statistics
            if (m_poly_apx_counter[p] == m_settings.apx_per_poly_limit)
                OCApproximationStatistics::get_instance().apx_too_often();
        #endif
        return false;
    }

    bool crit_involved_count(const std::vector<Atom>& constraints) {
        if (!m_settings.crit_apx_per_constraint_enabled) return true;
        bool res = true;
        for (const auto& c : constraints) {
            //++m_constraint_involved_counter[c];
            if (m_constraint_involved_counter[c] >= m_settings.apx_per_constraint_limit) {
                res = false;
                /*#ifdef SMTRAT_DEVOPTION_Statistics
                    if (m_constraint_involved_counter[c] == m_settings.crit_max_constraint_involved)
                        OCApproximationStatistics::get_instance().involved_too_often();
                #endif*/
            }
        }
        return res;
    }

    bool crit_side_degree(datastructures::Projections& proj, const IR& ir, datastructures::RootMap::const_iterator start, datastructures::RootMap::const_iterator end) {
        if (!m_settings.crit_side_enabled) return false;
        for(auto it = start; it != end; it++) {
            for (const auto& ir_outer : it->second) {
                if (ir.poly == ir_outer.root.poly) continue;
                if (crit_pair_degree(proj, ir, ir_outer.root)) return true;
            }
        }
        return false;
    }

    void new_cell(const std::vector<Atom>& constraints) {
        m_curr_constraints = constraints;
        m_currently_approximating = false;
    }


public:
    static ApxCriteria<Settings>& get_instance() {
        static ApxCriteria<Settings> ac;
        return ac;
    }


    static void inform(const Polynomial& p, std::size_t root_index) {
        ApxCriteria<Settings>& ac = get_instance();
        auto pr = std::make_pair(p, root_index);
        ++(ac.m_poly_apx_counter[pr]);
        if (!ac.m_currently_approximating) {
            ++ac.m_approximated_cells;
            ac.m_currently_approximating = true;
            for (const auto& c : ac.m_curr_constraints) {
                ++ac.m_constraint_involved_counter[c];
                #ifdef SMTRAT_DEVOPTION_Statistics
                    if (ac.m_constraint_involved_counter[c] == ac.m_settings.apx_per_constraint_limit)
                        OCApproximationStatistics::get_instance().involved_too_often();
                #endif
            }
        }
    }

    static bool cell(const std::vector<Atom>& constraints) {
        ApxCriteria& ac = get_instance();
        ac.new_cell(constraints);
        return ac.crit_considered_count() && ac.crit_apx_count() && ac.crit_involved_count(constraints);
    }

    static bool level(std::size_t lvl) {
        ApxCriteria& ac = get_instance();
        if (!ac.m_settings.crit_level_enabled) return true;
        return lvl > 1;
    }

    static bool poly(datastructures::Projections& proj, const IR& ir) {
        ApxCriteria& ac = get_instance();
        return ac.crit_single_degree(proj, ir) && ac.crit_poly_apx_count(proj, ir);
    }

    static bool poly_pair(datastructures::Projections& proj, const IR& ir_l, const IR& ir_u) {
        ApxCriteria& ac = get_instance();
        return (
               ac.crit_pair_degree(proj, ir_l, ir_u)
            && ac.crit_poly_apx_count(proj, ir_l)
            && ac.crit_poly_apx_count(proj, ir_u)
        );
    }

    static bool side(datastructures::Projections& proj, const IR& ir, datastructures::RootMap::const_iterator start, datastructures::RootMap::const_iterator end){
        if (poly(proj, ir)) return true;
        ApxCriteria& ac = get_instance();
        return ac.crit_side_degree(proj, ir, start, end);
    }
};

}