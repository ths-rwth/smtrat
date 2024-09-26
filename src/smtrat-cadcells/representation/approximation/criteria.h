#pragma once

#include <smtrat-cadcells/OCApproximationStatistics.h>
#include <smtrat-cadcells/datastructures/representation.h>

namespace smtrat::cadcells::representation::approximation {

using IR = datastructures::IndexedRoot;

template<typename Settings>
class Criteria {
private:
    bool m_currently_approximating = false;
    std::size_t m_approximated_cells = 0;
    std::size_t m_approximated_cells_since_block = 0;

    std::size_t m_blocking_next = 0;
    std::size_t m_blocking_increment = 0;

    std::unordered_map<Atom, std::size_t> m_constraint_involved_counter;
    std::vector<Atom> m_curr_constraints;

private:

    // Bookkeeping
    void new_cell(const std::vector<Atom>& constraints) {
        m_curr_constraints = constraints;
        m_currently_approximating = false;
    }


    /** Checks whether the current cell should be approximated based on the number of approx. cells.
     * 
     * @returns true if this criterion is disabled or if approximation is not currently blocked and
     * the number of approximated cells since the last blocking phase is below the set limit.
     * @returns false otherwise
     */
    bool crit_apx_count() {
        if (!Settings::crit_apx_cells_enabled) return true;
        if (m_blocking_next > 1) { // 1 instead of 0 because the very first blocked cell does not decrement this counter
            --m_blocking_next;
            return false;
        }
        if (m_approximated_cells_since_block == Settings::approximated_cells_limit) {
            SMTRAT_STATISTICS_CALL(apx_statistics().hit_approximation_limit());
            if (Settings::blocking > 0) {
                m_blocking_next = Settings::blocking + m_blocking_increment; // increment the number of blocked cells
                m_blocking_increment += Settings::blocking_increment; // the increment itself increases for the next time
                m_approximated_cells_since_block = 0;
            }
            return false;
        }

        return true;
    }


    /** Checks whether the current cell should be approximated based on the involved constraints.
     * 
     * @returns true if disabled or if a set percentage of given constraints was already involved in too many approximated cells.
     * @returns false otherwise
     */
    bool crit_involved_count(const std::vector<Atom>& constraints) {
        if (!Settings::crit_apx_per_constraint_enabled) return true;

        std::size_t critical_constraints = std::count_if(
            constraints.begin(), constraints.end(),
            [&](const auto& c){ return m_constraint_involved_counter[c] >= Settings::apx_per_constraint_limit; }
        );

        return (
               critical_constraints < constraints.size()
            && critical_constraints <= Settings::involved_constraint_scale * constraints.size()
        );
    }

public:

    static Criteria<Settings>& get() { static Criteria<Settings> ac; return ac; }


    // informs that the current cell was approximated
    void did_approximation() {
        if (m_currently_approximating) return;

        ++m_approximated_cells;
        ++m_approximated_cells_since_block;
        m_currently_approximating = true;

        if (Settings::crit_apx_per_constraint_enabled) { // apx per constraint book keeping
            for (const auto& c : m_curr_constraints) {
                ++m_constraint_involved_counter[c];
            }
        }
    }


    /// Checks whether the current cell should be approximated.
    /// Should only be called once per cell (for bookkeeping).
    bool cell(const std::vector<Atom>& constraints) {
        new_cell(constraints);
        return (
               crit_apx_count()
            && crit_involved_count(constraints)
        );
    }


    /// Checks whether the given level should be approximated 
    bool level(std::size_t lvl) {
        return !Settings::crit_level_enabled || lvl > 1;
    }


    /** Checks whether the given root should be approximated based on the degree of the polynomial.
     * 
     * The threshold for the degree is static if Settings::dynamic_degree_scale = 0.
     * Otherwise, the threshold grows with the number of approximated cells
     * (to discourage approximations leading to too many cells)
     */
    bool poly(datastructures::Projections& proj, const IR& ir) {
        std::size_t threshold = Settings::single_degree_threshold + (m_approximated_cells * Settings::dynamic_degree_scale)/10;
        return (
            !Settings::crit_single_degree_enabled || 
            (proj.degree(ir.poly) >= threshold)
        );
    }


    /** Checks whether the an approximation should be inserted between the two given roots,
     * based on the degree of the polynomials and the expected degree of their resultant.
     */
    bool poly_pair(datastructures::Projections& proj, const IR& ir_l, const IR& ir_u) {
        if (!Settings::crit_pair_degree_enabled) return true;
        std::size_t deg_l = proj.degree(ir_l.poly);
        if (deg_l <= 2) return false; // TODO: magic number
        std::size_t deg_u = proj.degree(ir_u.poly);
        if (deg_u <= 2) return false;
        return deg_l * deg_u >= Settings::pair_degree_threshold;
    }


    /** Checks whether a cell with the given sample should be approximated.
     *  If the sample has a large rational representation, the cell is probably already small and
     *  approximation might blow this up even more, which this criterion tries to avoid.
     */
    bool sample(const Rational& s) {
        if (!Settings::crit_sample_enabled) return true;
        static_assert(std::is_same<Rational, mpq_class>::value);
        return mpz_sizeinbase(s.get_den_mpz_t(), 2) + mpz_sizeinbase(s.get_num_mpz_t(), 2) <= Settings::sample_bitsize_limit;
    }


    /** Checks whether this side (upper/lower) of the cell should be approximated,
     * based on the bounds and potential resultants with other roots on that side
     */
    bool side(datastructures::Projections& proj, const IR& ir, datastructures::RootMap::const_iterator start, datastructures::RootMap::const_iterator end){
        // TODO: this returns true if the bound has large degree **OR** if (side enabled and there is an expensive pair)
        // TODO: what about **AND**? 
        if (poly(proj, ir)) return true;
        if (!Settings::crit_side_enabled) return false;
        for (auto it = start; it != end; ++it) {
            for (const auto& ir_outer : it->second) {
                if (ir.poly == ir_outer.root.poly) continue;
                if (poly_pair(proj, ir, ir_outer.root)) return true;
            }
        }
        return false;
    }


    bool covering() {
        return false; // TODO
    }
};

}