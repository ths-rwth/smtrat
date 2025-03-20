#pragma once


#include <smtrat-common/statistics/Statistics.h>
#include "types.h"

#ifdef SMTRAT_DEVOPTION_Statistics


namespace smtrat::covering_ng {

class CoveringNGStatistics : public Statistics {
    carl::statistics::Timer m_formula_evaluation;
    carl::statistics::Series m_implicant_sotd;
    std::size_t m_num_implicants_used;
    std::size_t m_num_implicants_found;
    std::size_t m_num_intervals_used;
    std::size_t m_num_intervals_found;
    std::size_t m_bool_var_not_at_end;
    std::size_t m_num_intervals_minim;

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
        Statistics::addKeyValuePair("intervals.minimization.num", m_num_intervals_minim);
        Statistics::addKeyValuePair("var_order.bool_var_not_at_end.num", m_bool_var_not_at_end);
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
    void minimization_intervals(std::size_t num) { m_num_intervals_minim += num; }

    void formula_evaluation_start() {
        m_formula_evaluation.start_this();
    }
    void formula_evaluation_end() {
        m_formula_evaluation.finish();
    }

    void variable_ordering(const cadcells::VariableOrdering& var_order, const std::map<carl::Variable, carl::Variable>& var_mapping) {
        bool last_block_bool = true;
        for (auto it = var_order.rbegin(); it != var_order.rend(); it++) {
            if (last_block_bool) {
                // if we are in the last block of booleans and see a non-Boolean variable, then we just left the last block consisting of booleans
                if (var_mapping.find(*it) == var_mapping.end()) last_block_bool = false;
            } else {
                // if we are not in the last block of booleans and we see a Boolean variable, then we increase the counter
                if (var_mapping.find(*it) != var_mapping.end()) m_bool_var_not_at_end++;
            }
        }
    }
   
};

CoveringNGStatistics &statistics();

}

#endif