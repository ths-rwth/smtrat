/**
 * Class to create a settings object for the SATModule.
 * @file SATSettings.h
 * @author Florian Corzilius
 * @since 2014-10-02
 * @version 2014-10-02
 */

#pragma once

#include "mcsat/MCSATSettings.h"

#include "VarSchedulerForwardDeclarations.h"
    
namespace smtrat {

enum class CCES : unsigned { SECOND_LEVEL_MINIMIZER, LITERALS_BLOCKS_DISTANCE, SECOND_LEVEL_MINIMIZER_PLUS_LBD };

enum class VARIABLE_ACTIVITY_STRATEGY : unsigned { NONE, MIN_COMPLEXITY_MAX_OCCURRENCES };

enum class MCSAT_BOOLEAN_DOMAIN_PROPAGATION : unsigned { NONE, PARTIAL_CONFLICT, PARTIAL, FULL};

struct SATSettings1 {
    static constexpr auto moduleName = "SATModule<SATSettings1>";
    static const bool allow_theory_propagation           = true;
    static const bool try_full_lazy_call_first           = false;
    static const bool use_restarts                       = true;
    static const bool stop_search_after_first_unknown    = false;
    static const bool formula_guided_decision_heuristic  = false;
    static const bool check_active_literal_occurrences   = false;
    static const bool check_if_all_clauses_are_satisfied = false;
    static const bool initiate_activities                = false;
    static const bool remove_satisfied                   = false; // This cannot be true as otherwise incremental sat solving won't work
    static constexpr double percentage_of_conflicts_to_add = 1.0;
    static constexpr CCES conflict_clause_evaluation_strategy = CCES::SECOND_LEVEL_MINIMIZER_PLUS_LBD;
    static constexpr VARIABLE_ACTIVITY_STRATEGY initial_variable_activities = VARIABLE_ACTIVITY_STRATEGY::NONE;
    static const bool mc_sat = false;
    static constexpr bool validate_clauses              = false;
    static constexpr bool check_for_duplicate_clauses   = false;
    static constexpr bool mcsat_resolve_clause_chains   = false;
    static constexpr bool mcsat_learn_lazy_explanations = false;
    static constexpr unsigned int mcsat_num_insert_assignments = 1;
    static constexpr MCSAT_BOOLEAN_DOMAIN_PROPAGATION mcsat_boolean_domain_propagation = MCSAT_BOOLEAN_DOMAIN_PROPAGATION::FULL;
    static constexpr bool mcsat_backjump_decide = true;
    using VarScheduler = VarSchedulerSMTTheoryGuided<TheoryGuidedDecisionHeuristicLevel::SATISFIED_FIRST>;
    using MCSATSettings = mcsat::MCSATSettingsDefault;
};

struct SATSettings3 : SATSettings1 {
    static const bool remove_satisfied = false;
};

struct SATSettingsStopAfterUnknown : SATSettings1 {
    static const bool stop_search_after_first_unknown = true;
};

struct SATSettingsMCSAT : SATSettings1 {
    static const bool mc_sat = true;
    // static const bool check_active_literal_occurrences = true;
    // needed for variable scheduling to work:
    // using VarScheduler = VarSchedulerMcsatTheoryFirst<TheoryVarSchedulerStatic<mcsat::VariableOrdering::FeatureBasedBrown>>;
    // using VarScheduler = VarSchedulerMcsatBooleanFirst<mcsat::VariableOrdering::FeatureBased>;
    // using VarScheduler = VarSchedulerMcsatUnivariateClausesOnly<TheoryVarSchedulerStatic<mcsat::VariableOrdering::FeatureBased>,false>;
    // using VarScheduler = VarSchedulerMcsatTheoryFirst<VarSchedulerMinisat>;
    // using VarScheduler = VarSchedulerMcsatUnivariateConstraintsOnly<1, mcsat::VariableOrdering::FeatureBased>;
    // using VarScheduler = VarSchedulerMcsatActivityPreferTheory<mcsat::VariableOrdering::FeatureBased>;

    // uniform (resp Boolean and theory vars) decision heuristic
    // Note: mcsat_backjump_decide needs to be activated, otherwise we run into termination problems!
    static constexpr bool mcsat_backjump_decide = true;
    using VarScheduler = VarSchedulerMinisat;
    // using VarScheduler = VarSchedulerFixedRandom;
};

struct SATSettingsMCSATDefault : SATSettingsMCSAT {
    static constexpr auto moduleName = "SATModule<SATSettingsMCSATDefault>";
    using MCSATSettings = mcsat::MCSATSettingsDefault;
};

struct SATSettingsMCSATOC : SATSettingsMCSAT {
    static constexpr auto moduleName = "SATModule<MCSATOC>";
    using MCSATSettings = mcsat::MCSATSettingsOC;
};

}
