#pragma once

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat::cadcells {

class OCApproximationStatistics : public Statistics {
private:
    using Counter = std::map<std::size_t, std::size_t>;

    bool m_currently_approximated = false; // helper variable: is the current cell approximated?

    std::size_t m_considered_cells           = 0;   // #calls using the approximation heuristic
    std::size_t m_approximated_cells         = 0;   // #calls actually approximating
    std::size_t m_approximated_cells_success = 0;   // #successful calls actually approximating

    Counter m_approximated_degree_counter;          // Counts approximations for each degree

    std::vector<std::pair<std::size_t,std::size_t>>  m_taylor_ignored; // For each taylor-approximated polynomial, #variables left out and # variables
    std::size_t m_taylor_grad_zero = 0; // #times the taylor method fails because of gradient 0

    std::size_t m_unbounded_levels      = 0;     // #unbounded levels in the constructed cells
    std::size_t m_half_unbounded_levels = 0;     // #one side unbounded levels in the constructed cells
    std::vector<std::size_t> m_cell_dimensions;  // Dimension of the constructed cells

    std::size_t m_involved_too_often = 0;     // #times a constraint was involved in too many conflicts
    bool m_max_apx_reached           = false; // flag whether the max number of apx is reached

    std::size_t m_irrational_sample                   = 0; // #times a sample was irrational
    std::size_t m_pwl_approximation                   = 0; // #times a pwl approximation was used
    std::size_t m_pwl_left_intersection               = 0; // #times a linear segment on the left had an intersection with the polynomial
    std::size_t m_pwl_right_intersection              = 0; // #times a linear segment on the right had an intersection with the polynomial
    std::size_t m_pwl_fallback_univariate             = 0; // #times a fallback was used because the polynomial was univariate
    std::size_t m_pwl_fallback_level_too_low          = 0; // #times a fallback was used because the level was too low
    std::size_t m_pwl_fallback_primary_irrational     = 0; // #times a fallback was used because the primary sample was irrational
    std::size_t m_pwl_fallback_no_delineable_space    = 0; // #times a fallback was used because there was no space in the delineable interval
    std::size_t m_pwl_fallback_no_delineable_interval = 0; // #times a fallback was used because no delineable interval was found

    double safe_divide(double divident, double divisor) {
        return (divisor == 0.0) ? 0.0 : (divident / divisor);
    }

    void collect_counter_stats(const std::string& name, const Counter& c) {
        std::size_t max = 0;
        std::size_t n = 0;
        std::size_t sum = 0;
        for (const auto& [key, value] : c) {
            n += value;
            sum += key * value;
            if (key > max) max = key;
        }
        double mean = safe_divide((double) sum, (double) n);
        Statistics::addKeyValuePair("total_"+name, n);
        Statistics::addKeyValuePair("max_"+name, max);
        Statistics::addKeyValuePair("mean_"+name, mean);
    }

public:
    bool enabled() const { return true; }

    void collect() {
        Statistics::addKeyValuePair("considered",   m_considered_cells);
        Statistics::addKeyValuePair("approximated", m_approximated_cells);
        Statistics::addKeyValuePair("success",      m_approximated_cells_success);

        collect_counter_stats("apx_degrees", m_approximated_degree_counter);

        Statistics::addKeyValuePair("unbounded_levels",                    m_unbounded_levels);
        Statistics::addKeyValuePair("half_unbounded_levels",               m_half_unbounded_levels);
        
        std::size_t sumDimensions = 0;
        for (const std::size_t d : m_cell_dimensions) sumDimensions += d;
        double mean_cell_dim = safe_divide((double) sumDimensions, (double) m_cell_dimensions.size());

        Statistics::addKeyValuePair("mean_cell_dimension",                 mean_cell_dim);

        std::size_t maxIgnoredVars = 0;
        double sum = 0.0;
        std::size_t total = 0;
        for (const auto& item : m_taylor_ignored) {
            sum += safe_divide((double) item.first, (double) item.second);
            total += item.first;
            if (item.first > maxIgnoredVars) maxIgnoredVars = item.first;
        }
        double meanIgnoredVars = safe_divide(sum, (double) m_taylor_ignored.size());

        Statistics::addKeyValuePair("max_taylor_ignored_vars",             maxIgnoredVars);
        Statistics::addKeyValuePair("total_taylor_ignored_vars",           total);
        Statistics::addKeyValuePair("mean_taylor_ignored_vars",            meanIgnoredVars);
        Statistics::addKeyValuePair("taylor_failure",                      m_taylor_grad_zero);

        Statistics::addKeyValuePair("involved_too_often",                  m_involved_too_often);
        Statistics::addKeyValuePair("max_apx_reached",                     m_max_apx_reached);

        Statistics::addKeyValuePair("irrational_sample",                   m_irrational_sample);
        Statistics::addKeyValuePair("pwl_approximation",                   m_pwl_approximation);
        Statistics::addKeyValuePair("pwl_left_intersection",               m_pwl_left_intersection);
        Statistics::addKeyValuePair("pwl_right_intersection",              m_pwl_right_intersection);
        Statistics::addKeyValuePair("pwl_fallback_univariate",             m_pwl_fallback_univariate);
        Statistics::addKeyValuePair("pwl_fallback_level_too_low",          m_pwl_fallback_level_too_low);
        Statistics::addKeyValuePair("pwl_fallback_primary_irrational",     m_pwl_fallback_primary_irrational);
        Statistics::addKeyValuePair("pwl_fallback_no_delineable_space",    m_pwl_fallback_no_delineable_space);
        Statistics::addKeyValuePair("pwl_fallback_no_delineable_interval", m_pwl_fallback_no_delineable_interval);
    }

    void new_cell() {
        m_currently_approximated = false;
    }

    void success(std::size_t d) {
        if (m_currently_approximated) ++m_approximated_cells_success;
        m_cell_dimensions.push_back(d);
    }
    void approximation_considered(bool is_considered) { if (is_considered) ++m_considered_cells; }
    void approximated(std::size_t d) {
        ++m_approximated_degree_counter[d];
        if (!m_currently_approximated) {
            ++m_approximated_cells;
             m_currently_approximated = true;
        }
    }

    void taylor_ignored_vars(std::size_t ignored, std::size_t total) {m_taylor_ignored.emplace_back(ignored, total); }
    void taylor_failure() { ++m_taylor_grad_zero; }

    void unbounded_level()      { ++m_unbounded_levels; }
    void half_unbounded_level() { ++m_half_unbounded_levels; }
    void cell_dimension(std::size_t d) { m_cell_dimensions.push_back(d); }

    void involved_too_often()       { ++m_involved_too_often; }
    void hit_approximation_limit()  { m_max_apx_reached = true; }

    void irrational_sample()                   { ++m_irrational_sample; }
    void pwl_approximation()                   { ++m_pwl_approximation; }
    void pwl_left_intersection()               { ++m_pwl_left_intersection; }
    void pwl_right_intersection()              { ++m_pwl_right_intersection; }
    void pwl_fallback_univariate()             { ++m_pwl_fallback_univariate; }
    void pwl_fallback_level_too_low()          { ++m_pwl_fallback_level_too_low; }
    void pwl_fallback_primary_irrational()     { ++m_pwl_fallback_primary_irrational; }
    void pwl_fallback_no_delineable_space()    { ++m_pwl_fallback_no_delineable_space; }
    void pwl_fallback_no_delineable_interval() { ++m_pwl_fallback_no_delineable_interval; }
};

OCApproximationStatistics &apx_statistics() {
    static OCApproximationStatistics &stats = statistics_get<OCApproximationStatistics>("approximation");
    return stats;
}

}

#endif