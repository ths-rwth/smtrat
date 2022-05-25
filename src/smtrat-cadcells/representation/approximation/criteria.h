#pragma once
#include <carl/util/Singleton.h>

namespace smtrat::cadcells::representation::approximation {

using IR = datastructures::IndexedRoot;

class ApxCriteria : public carl::Singleton<ApxCriteria> {
    friend Singleton<ApxCriteria>;
    private:
        std::size_t m_considered_count = 0;
        std::size_t m_apx_count = 0;
        bool m_curr_apx = false;
        std::unordered_map<FormulaT, std::size_t> m_constraint_involved_counter;
        std::map<Poly, std::size_t> m_poly_apx_counter;

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
            Poly p = proj.polys()(ir.poly);
            if (m_poly_apx_counter[p] < apx_settings().crit_max_apx_per_poly) return true;
            #ifdef SMTRAT_DEVOPTION_Statistics
                if (m_poly_apx_counter[p] == apx_settings().crit_max_apx_per_poly)
                    OCApproximationStatistics::get_instance().apxTooOften();
            #endif
            return false;
        }

        bool crit_involved_count(const FormulasT& constraints) {
            if (!apx_settings().crit_involved_count_enabled) return true;
            bool res = true;
            for (const auto& c : constraints) {
                ++m_constraint_involved_counter[c];
                if (m_constraint_involved_counter[c] >= apx_settings().crit_max_constraint_involved) {
                    res = false;
                    #ifdef SMTRAT_DEVOPTION_Statistics
                        if (m_constraint_involved_counter[c] == apx_settings().crit_max_constraint_involved)
                            OCApproximationStatistics::get_instance().involvedTooOften();
                    #endif
                }
            }
            return res;
        }

        bool crit_side_degree(datastructures::Projections& proj, const IR& ir, datastructures::RootMap::const_iterator start, datastructures::RootMap::const_iterator end) {
            if (!apx_settings().crit_side_degree_enabled) return false;
            for(auto it = start; it != end; it++) {
                for (const auto& ir_outer : it->second) {
                    if (ir.poly == ir_outer.poly) continue;
                    if (crit_pair_degree(proj, ir, ir_outer)) return true;
                }
            }
            return false;
        }

        void new_cell() {
            m_curr_apx = false;
        }


    public:
        static void inform(const Poly& p) {
            ApxCriteria& ac = getInstance();
            ++(ac.m_poly_apx_counter[p]);
            if (!ac.m_curr_apx) {
                ++ac.m_apx_count;
                ac.m_curr_apx = true;
            }
        }

        static bool cell(const FormulasT& constraints) {
            ApxCriteria& ac = getInstance();
            ac.new_cell();
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