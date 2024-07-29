/**
 * @file SimplexStatistics.h
 * @author Valentin Promies
 *
 * @version 2023-05-17
 * Created on 2023-05-17.
 */


#pragma once

#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat {

class SimplexStatistics : public Statistics {
private:
    std::size_t  m_total_pivots        = 0;
    std::size_t  m_curr_pivots         = 0;
    std::size_t  m_max_pivots          = 0;
    std::size_t  m_checks_with_pivot   = 0;
    std::size_t  m_tableau_size        = 0;
    std::size_t  m_tableau_entries     = 0;
    std::size_t  m_refinements         = 0;
    std::size_t  m_conflicts           = 0;
    std::size_t  m_sum_conflict_sizes  = 0;
    std::size_t  m_theory_lemmas       = 0; // excluding splitting lemmas
    std::size_t  m_theory_propagations = 0;
    std::size_t  m_checks              = 0;
    std::size_t  m_sum_check_sizes     = 0;
    std::size_t  m_neq_splits          = 0;

    inline double safe_divide(std::size_t divident, std::size_t divisor) {
        return (divisor == 0) ? 0.0 : (static_cast<double>(divident) / static_cast<double>(divisor));
    }

public:
    // Override Statistics::collect.
    void collect() {
        addKeyValuePair( "total_pivots",        m_total_pivots);
        addKeyValuePair( "max_pivots",          m_max_pivots);
        addKeyValuePair( "average_pivots",      safe_divide(m_total_pivots, m_checks_with_pivot));
        addKeyValuePair( "tableau_size",        m_tableau_size);
        addKeyValuePair( "tableau_entries",     m_tableau_entries);
        addKeyValuePair( "tableau_coverage",    safe_divide(m_tableau_entries, m_tableau_size));
        addKeyValuePair( "refinements",         m_refinements);
        addKeyValuePair( "conflicts",           m_conflicts);
        addKeyValuePair( "avg_conflict_size",   safe_divide(m_sum_conflict_sizes, m_conflicts));
        addKeyValuePair( "lemmas",              m_theory_lemmas);
        addKeyValuePair( "theory_propagations", m_theory_propagations);
        addKeyValuePair( "checks",              m_checks);
        addKeyValuePair( "checks_with_pivots",  m_checks_with_pivot);
        addKeyValuePair( "avg_check_size",      safe_divide(m_sum_check_sizes, m_checks));
        addKeyValuePair( "neq_splits",          m_neq_splits);
    }

    void pivot() {
        ++m_total_pivots;
        ++m_curr_pivots;
    }

    void check(const ModuleInput& _formula) {
        if (m_curr_pivots > 0) {
            if (m_curr_pivots > m_max_pivots) {
                m_max_pivots = m_curr_pivots;
            }
            ++m_checks_with_pivot;
            m_curr_pivots = 0;
        }

        ++m_checks;
        m_sum_check_sizes += _formula.size();
    }

    void conflict(const std::vector<FormulaSetT>& inf_subsets) {
        m_conflicts += inf_subsets.size();
        for (const auto& s : inf_subsets) m_sum_conflict_sizes += s.size();
    }

    void lemma()              { ++m_theory_lemmas;       }
    void theory_propagation() { ++m_theory_propagations; }
    void refinement()         { ++m_refinements;         }
    void neq_split()          { ++m_neq_splits;          }

    void tableau_size(size_t size) { m_tableau_size = size; }
    void tableau_entries(size_t n) { m_tableau_entries = n; }
};

} // namespace smtrat

#endif
