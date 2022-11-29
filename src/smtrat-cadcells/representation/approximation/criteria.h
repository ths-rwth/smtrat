#pragma once
#include <carl-common/memory/Singleton.h>

namespace smtrat::cadcells::representation::approximation {

using IR = datastructures::IndexedRoot;

class ApxCriteria : public carl::Singleton<ApxCriteria> {
    friend Singleton<ApxCriteria>;
    private:
        std::size_t m_considered_count = 0;
        std::size_t m_apx_count = 0;
        bool m_curr_apx = false;
        std::unordered_map<Atom, std::size_t> m_constraint_involved_counter;
        std::map<std::pair<Polynomial,  std::size_t>, std::size_t> m_poly_apx_counter;
        std::vector<Atom> m_curr_constraints;

        bool crit_considered_count() {
            if (!apx_settings().crit_considered_count_enabled) return true;
            if (m_considered_count < apx_settings().crit_max_considered) return true;
            #ifdef SMTRAT_DEVOPTION_Statistics
                OCApproximationStatistics::get_instance().maxConsideredReached();
            #endif
            return false; 
        }

        bool crit_apx_count() {
            if (!apx_settings().crit_apx_count_enabled) return true;
            if (m_apx_count < apx_settings().crit_max_apx) return true;
            #ifdef SMTRAT_DEVOPTION_Statistics
                OCApproximationStatistics::get_instance().maxApxReached();
            #endif
            return false; 
        }

        bool crit_single_degree(datastructures::Projections& proj, const IR& ir) {
            if (!apx_settings().crit_single_degree_enabled) return true;
            return proj.degree(ir.poly) >= apx_settings().crit_degree_threshold;
        }

        bool crit_pair_degree(datastructures::Projections& proj, const IR& ir_l, const IR& ir_u) {
            if (!apx_settings().crit_pair_degree_enabled) return true;
            std::size_t deg_l = proj.degree(ir_l.poly);
            if (deg_l <= apx_settings().taylor_deg) return false;
            std::size_t deg_u = proj.degree(ir_u.poly);
            if (deg_u <= apx_settings().taylor_deg) return false;
            return deg_l * deg_u >= 2*apx_settings().crit_degree_threshold;
        }

        bool crit_poly_apx_count(datastructures::Projections& proj, const IR& ir) {
            if (!apx_settings().crit_poly_apx_count_enabled) return true;
            auto p = std::make_pair(proj.polys()(ir.poly), ir.index);
            if (m_poly_apx_counter[p] < apx_settings().crit_max_apx_per_poly) return true;
            #ifdef SMTRAT_DEVOPTION_Statistics
                if (m_poly_apx_counter[p] == apx_settings().crit_max_apx_per_poly)
                    OCApproximationStatistics::get_instance().apxTooOften();
            #endif
            return false;
        }

        bool crit_involved_count(const std::vector<Atom>& constraints) {
            if (!apx_settings().crit_involved_count_enabled) return true;
            bool res = true;
            for (const auto& c : constraints) {
                //++m_constraint_involved_counter[c];
                if (m_constraint_involved_counter[c] >= apx_settings().crit_max_constraint_involved) {
                    res = false;
                    /*#ifdef SMTRAT_DEVOPTION_Statistics
                        if (m_constraint_involved_counter[c] == apx_settings().crit_max_constraint_involved)
                            OCApproximationStatistics::get_instance().involvedTooOften();
                    #endif*/
                }
            }
            return res;
        }

        bool crit_side_degree(datastructures::Projections& proj, const IR& ir, datastructures::RootMap::const_iterator start, datastructures::RootMap::const_iterator end) {
            if (!apx_settings().crit_side_degree_enabled) return false;
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
            m_curr_apx = false;
        }


    public:
        static void inform(const Polynomial& p, std::size_t root_index) {
            ApxCriteria& ac = getInstance();
            auto pr = std::make_pair(p, root_index);
            ++(ac.m_poly_apx_counter[pr]);
            if (!ac.m_curr_apx) {
                ++ac.m_apx_count;
                ac.m_curr_apx = true;
                for (const auto& c : ac.m_curr_constraints) {
                    ++ac.m_constraint_involved_counter[c];
                    #ifdef SMTRAT_DEVOPTION_Statistics
                        if (ac.m_constraint_involved_counter[c] == apx_settings().crit_max_constraint_involved)
                            OCApproximationStatistics::get_instance().involvedTooOften();
                    #endif
                }
            }
        }

        static bool cell(const std::vector<Atom>& constraints) {
            ApxCriteria& ac = getInstance();
            ac.new_cell(constraints);
            return ac.crit_considered_count() && ac.crit_apx_count() && ac.crit_involved_count(constraints);
        }

        static bool level(std::size_t lvl) {
            if (!apx_settings().crit_level_enabled) return true;
            return lvl > 1;
        }

        static bool poly(datastructures::Projections& proj, const IR& ir) {
            ApxCriteria& ac = getInstance();
            return ac.crit_single_degree(proj, ir) && ac.crit_poly_apx_count(proj, ir);
        }

        static bool poly_pair(datastructures::Projections& proj, const IR& ir_l, const IR& ir_u) {
            ApxCriteria& ac = getInstance();
            return ac.crit_pair_degree(proj, ir_l, ir_u) && ac.crit_poly_apx_count(proj, ir_l) && ac.crit_poly_apx_count(proj, ir_u);
        }

        static bool side(datastructures::Projections& proj, const IR& ir, datastructures::RootMap::const_iterator start, datastructures::RootMap::const_iterator end){
            if (poly(proj, ir)) return true;
            ApxCriteria& ac = getInstance();
            return ac.crit_side_degree(proj, ir, start, end);
        }
};

}