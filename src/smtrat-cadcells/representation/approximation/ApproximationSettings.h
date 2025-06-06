#include "ran_approximation.h"
#include "polynomials.h"

namespace smtrat::cadcells::representation::approximation {

struct BaseSamplingRatioSettings {
    static constexpr double root_ratio_lower = 0.75;
    static constexpr double root_ratio_upper = 0.875;
};


struct BaseSamplingSternBrocotSettings {
    static constexpr std::size_t n_iterations = 2;
};


struct SimpleSettings {
    using Sampling = SampleSimple;
};


struct BaseTaylorSettings {
    using Sampling = SampleFixedRatio<BaseSamplingRatioSettings>;

    static constexpr std::size_t taylor_degree = 1;
};

// TODO: this is so far away from the actual criteria and dynamic settings
struct BaseCriteriaSettings {
    static constexpr std::size_t approximated_cells_limit = 50;
    static constexpr std::size_t blocking                 = 0;
    static constexpr std::size_t blocking_increment       = 1;
    static constexpr std::size_t apx_per_constraint_limit = 10;
    static constexpr double      involved_constraint_scale = 10;  
    static constexpr std::size_t single_degree_threshold  = 5;
    static constexpr std::size_t dynamic_degree_scale     = 0;
    static constexpr std::size_t pair_degree_threshold    = 7;
    static constexpr std::size_t sample_bitsize_limit     = 32;

    static constexpr bool crit_level_enabled              = false;
    static constexpr bool crit_apx_cells_enabled          = true;
    static constexpr bool crit_single_degree_enabled      = true;
    static constexpr bool crit_pair_degree_enabled        = false;
    static constexpr bool crit_apx_per_constraint_enabled = false;
    static constexpr bool crit_side_enabled               = false;
    static constexpr bool crit_sample_enabled             = false;
};

}