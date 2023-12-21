#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/statistics/Statistics.h>
#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat::qe {

class FMplexQEStatistics : public Statistics
{
private:
    std::size_t m_input_constraints  = 0;
    std::size_t m_eliminated_vars    = 0;
    std::size_t m_eliminated_by_eq   = 0;
    std::size_t m_output_constraints = 0;
    std::size_t m_total_constraints  = 0;
    std::size_t m_visited_nodes      = 0;
    std::size_t m_split_tried        = 0;
    std::size_t m_split_done         = 0;
    bool        m_eq_conflict        = false;
    carl::statistics::timer m_qe_timer;


public:
    void collect() {
        addKeyValuePair("input-constraints",  m_input_constraints);
        addKeyValuePair("eliminated-vars",    m_eliminated_vars);
        addKeyValuePair("eliminated-by-eq",   m_eliminated_by_eq);
        addKeyValuePair("output-constraints", m_output_constraints);
        addKeyValuePair("total-constraints",  m_total_constraints);
        addKeyValuePair("visited-nodes",      m_visited_nodes);
        addKeyValuePair("qe-called",          m_qe_timer);
        addKeyValuePair("eq-conflict",        m_eq_conflict);
        addKeyValuePair("split-tried",        m_split_tried);
        addKeyValuePair("split_done",         m_split_done);
    }

    auto& timer() { return m_qe_timer; }
    
    void   input(std::size_t n) { m_input_constraints  = n; }
    void    vars(std::size_t n) { m_eliminated_vars    = n; }
    void elim_eq(std::size_t n) { m_eliminated_by_eq   = m_eliminated_vars - n; }
    void  output(std::size_t n) { m_output_constraints = n; }
    void    node(std::size_t n) { ++m_visited_nodes; m_total_constraints += n; }
    void split_tried()          { ++m_split_tried; }
    void split_done()           { ++m_split_done; }
    
    void eq_conflict() { m_eq_conflict = true; }


    static FMplexQEStatistics& get_instance() {
        static FMplexQEStatistics & statistics = statistics_get<FMplexQEStatistics>("fmplex-qe");
		return statistics;
    }
};

}

#endif