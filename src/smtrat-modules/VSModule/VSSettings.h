/**
 * Class to create a settings object for the VSModule.
 * @author Florian Corzilius
 * @since 2013-07-02
 * @version 2014-09-18
 */

#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-modules/ModuleSettings.h>
    
namespace smtrat
{
    enum class VariableValuationStrategy : unsigned { OPTIMIZE_BEST, OPTIMIZE_AVERAGE, OPTIMIZE_WORST };
    
    struct VSSettings1 : ModuleSettings
    {
		static constexpr auto moduleName = "VSModule<VSSettings1>";
        static const bool elimination_with_factorization                        = false;
        static const bool local_conflict_search                                 = false;
        static const bool use_backjumping                                       = true;
        static const bool use_strict_inequalities_for_test_candidate_generation = true;
        #ifdef SMTRAT_VS_VARIABLEBOUNDS
        static const bool use_variable_bounds                                   = true;
        #else
        static const bool use_variable_bounds                                   = false;
        #endif
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
    };
    
    struct VSSettings2 : VSSettings1
    {
		static constexpr auto moduleName = "VSModule<VSSettings2>";
        static const bool elimination_with_factorization                        = true;
    };
    
    struct VSSettings23 : VSSettings2
    {
		static constexpr auto moduleName = "VSModule<VSSettings23>";
        static const bool local_conflict_search                                 = true;
    };
    
    struct VSSettings234 : VSSettings23
    {
		static constexpr auto moduleName = "VSModule<VSSettings234>";
        static const bool check_conflict_for_side_conditions                    = true;
        static const bool prefer_equation_over_all                              = true;
    };
    
    struct VSSettings2346 : VSSettings234
    {
		static constexpr auto moduleName = "VSModule<VSSettings2346>";
        static const bool use_branch_and_bound                                  = false;
        static const bool branch_and_bound_at_origin                            = false;
    };
    
    struct VSSettings2345 : VSSettings234
    {
		static constexpr auto moduleName = "VSModule<VSSettings2345>";
        static const bool sturm_sequence_for_root_check                         = use_variable_bounds && true;
    };
    
    struct VSSettings235 : VSSettings23
    {
		static constexpr auto moduleName = "VSModule<VSSettings235>";
        static const bool sturm_sequence_for_root_check                         = use_variable_bounds && true;
    };
    
    struct VSSettings24 : VSSettings2
    {
		static constexpr auto moduleName = "VSModule<VSSettings24>";
        static const bool check_conflict_for_side_conditions                    = true;
        static const bool prefer_equation_over_all                              = true;
    };
    
    struct VSSettings245 : VSSettings24
    {
		static constexpr auto moduleName = "VSModule<VSSettings245>";
        static const bool sturm_sequence_for_root_check                         = use_variable_bounds && true;
    };
    
    struct VSSettings25 : VSSettings2
    {
		static constexpr auto moduleName = "VSModule<VSSettings25>";
        static const bool sturm_sequence_for_root_check                         = use_variable_bounds && true;
    };
    
    struct VSSettings3 : VSSettings1
    {
		static constexpr auto moduleName = "VSModule<VSSettings3>";
        static const bool local_conflict_search                                 = true;
    };
    
    struct VSSettings34 : VSSettings3
    {
		static constexpr auto moduleName = "VSModule<VSSettings34>";
        static const bool check_conflict_for_side_conditions                    = true;
        static const bool prefer_equation_over_all                              = true;
    };
    
    struct VSSettings345 : VSSettings34
    {
		static constexpr auto moduleName = "VSModule<VSSettings345>";
        static const bool sturm_sequence_for_root_check                         = use_variable_bounds && true;
    };
    
    struct VSSettings35 : VSSettings3
    {
		static constexpr auto moduleName = "VSModule<VSSettings35>";
        static const bool sturm_sequence_for_root_check                         = use_variable_bounds && true;
    };
    
    struct VSSettings4 : VSSettings1
    {
		static constexpr auto moduleName = "VSModule<VSSettings4>";
        static const bool check_conflict_for_side_conditions                    = true;
        static const bool prefer_equation_over_all                              = true;
    };
    
    struct VSSettings45 : VSSettings4
    {
		static constexpr auto moduleName = "VSModule<VSSettings45>";
        static const bool sturm_sequence_for_root_check                         = use_variable_bounds && true;
    };
    
    struct VSSettings5 : VSSettings1
    {
		static constexpr auto moduleName = "VSModule<VSSettings5>";
        static const bool sturm_sequence_for_root_check                         = use_variable_bounds && true;
    };
    
    struct VSSettingsPlain : VSSettings1
    {
        static constexpr auto moduleName = "VSModule<VSSettingsPlain>";
        static const bool use_variable_bounds                                   = false;
        static const bool use_fixed_variable_order                              = false;
        static const bool local_conflict_search                                 = false;
        static const bool use_backjumping                                       = false;
    };
    
    struct VSSettingsNotSMTCompliant : VSSettingsPlain
    {
        static constexpr auto moduleName = "VSModule<VSSettingsNotSMTCompliant>";
        static const bool incremental_solving                                   = false;
        static const bool infeasible_subset_generation                          = false;
    };
    
    struct VSSettingsOnlyInc : VSSettingsNotSMTCompliant
    {
        static constexpr auto moduleName = "VSModule<VSSettingsOnlyInc>";
        static const bool incremental_solving                                   = true;
    };
    
    struct VSSettingsOnlyIS : VSSettingsNotSMTCompliant
    {
        static constexpr auto moduleName = "VSModule<VSSettingsOnlyIS>";
        static const bool infeasible_subset_generation                          = true;
    };
    
    struct VSSettingsOnlyVB : VSSettingsPlain
    {
        static constexpr auto moduleName = "VSModule<VSSettingsOnlyVB>";
        static const bool use_variable_bounds                                   = true;
    };
    
    struct VSSettingsOnlyLC : VSSettingsPlain
    {
        static constexpr auto moduleName = "VSModule<VSSettingsOnlyLC>";
        static const bool local_conflict_search                                 = true;
    };
    
    struct VSSettingsOnlyBJ : VSSettingsPlain
    {
        static constexpr auto moduleName = "VSModule<VSSettingsOnlyBJ>";
        static const bool use_backjumping                                       = true;
    };
}
