/**
 * Class to create a settings object for the VSModule.
 * @author Florian Corzilius
 * @since 2013-07-02
 * @version 2014-09-18
 */

#pragma once

#include <smtrat-common/smtrat-common.h>
    
namespace smtrat
{
    enum class VariableValuationStrategy : unsigned { OPTIMIZE_BEST, OPTIMIZE_AVERAGE, OPTIMIZE_WORST };
    
    struct VSSettings1
    {
		static constexpr auto moduleName = "VSModule<VSSettings1>";
        static const bool elimination_with_factorization                        = false;
        static const bool local_conflict_search                                 = false;
        static const bool use_backjumping                                       = true;
        static const bool use_strict_inequalities_for_test_candidate_generation = true;
        static const bool use_variable_bounds                                   = true;
        // static const bool use_variable_bounds                                   = false;
        static const bool sturm_sequence_for_root_check                         = use_variable_bounds && false;
        static const bool check_conflict_for_side_conditions                    = false;
        static const bool incremental_solving                                   = true;
        static const bool infeasible_subset_generation                          = true;
        static const bool virtual_substitution_according_paper                  = false;
        static const bool prefer_equation_over_all                              = false;
        static const bool mixed_int_real_constraints_allowed                    = false;
        static const bool split_neq_constraints                                 = false;
        static const size_t int_max_range                                       = 1;
        static const size_t lazy_check_threshold                                = 1;
        static const bool try_first_lazy                                        = false;
        static const bool use_branch_and_bound                                  = true;
        static const bool only_split_in_final_call                              = true;
        static const bool branch_and_bound_at_origin                            = false;
        static const bool use_fixed_variable_order                              = false;
        static constexpr auto variable_valuation_strategy = VariableValuationStrategy::OPTIMIZE_BEST;

		static constexpr bool make_constraints_strict_for_backend = true;
    };
        
    struct VSSettings234 : VSSettings1
    {
		static constexpr auto moduleName = "VSModule<VSSettings234>";
        static const bool elimination_with_factorization                        = true;
        static const bool local_conflict_search                                 = true;
        static const bool check_conflict_for_side_conditions                    = true;
        static const bool prefer_equation_over_all                              = true;
    };
	    
}
