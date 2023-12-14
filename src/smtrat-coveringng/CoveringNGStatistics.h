#pragma once


#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics


namespace smtrat::covering_ng {

class CoveringNGStatistics : public Statistics {
    carl::statistics::Timer m_formula_evaluation;
    carl::statistics::Series m_implicant_sotd;
    std::size_t m_num_implicants_used;
    std::size_t m_num_implicants_found;
    std::size_t m_num_intervals_used;
    std::size_t m_num_intervals_found;

public:
    bool enabled() const {
        return true;
    }

    void collect() {
        Statistics::addKeyValuePair("formula_evaluation", m_formula_evaluation);
        Statistics::addKeyValuePair("implicants.used.sotd", m_implicant_sotd);
        Statistics::addKeyValuePair("implicants.used.num", m_num_implicants_used);
        Statistics::addKeyValuePair("implicants.found.num", m_num_implicants_found);
        Statistics::addKeyValuePair("intervals.used.num", m_num_intervals_used);
        Statistics::addKeyValuePair("intervals.found.num", m_num_intervals_found);
    }

    void implicant_used(std::size_t sotd) {
        m_num_implicants_used++;
        m_implicant_sotd.add(sotd);
    }
    void implicants_found(std::size_t num) {
        m_num_implicants_found+=num;
    }
    void intervals_used(std::size_t num) {
        m_num_intervals_used+=num;
    }
    void intervals_found(std::size_t num) {
        m_num_intervals_found+=num;
    }

    void formula_evaluation_start() {
        m_formula_evaluation.start_this();
    }
    void formula_evaluation_end() {
        m_formula_evaluation.finish();
    }
   
};

CoveringNGStatistics &statistics();

}

#endif