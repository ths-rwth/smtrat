/**
 * Class to create a settings object for the SATModule.
 * @file SATSettings.h
 * @author Florian Corzilius
 * @since 2014-10-02
 * @version 2014-10-02
 */

#pragma once

#include "../../solver/ModuleSettings.h"

#include "mcsat/MCSATSettings.h"

#include "VarScheduling.h"
    
namespace smtrat
{
    enum class TheoryGuidedDecisionHeuristicLevel : unsigned { CONFLICT_FIRST, SATISFIED_FIRST, DISABLED };
    
    enum class CCES : unsigned { SECOND_LEVEL_MINIMIZER, LITERALS_BLOCKS_DISTANCE, SECOND_LEVEL_MINIMIZER_PLUS_LBD };
    
    enum class VARIABLE_ACTIVITY_STRATEGY : unsigned { NONE, MIN_COMPLEXITY_MAX_OCCURRENCES };
    
    struct SATSettings1 : ModuleSettings
    {
		static constexpr auto moduleName = "SATModule<SATSettings1>";
        /**
         * 
         */
        static const bool allow_theory_propagation = true;
        /**
         * 
         */
        static const bool try_full_lazy_call_first = false;
        /**
         * 
         */
        static const bool use_restarts = true;
        /**
         * 
         */
        static const bool stop_search_after_first_unknown = false;
        /**
         * 
         */
        static const bool formula_guided_decision_heuristic = false;
        /**
         * 
         */
        static const bool check_active_literal_occurrences = false;
        /**
         * 
         */
        static const bool check_if_all_clauses_are_satisfied = false;
        /**
         * 
         */
        static const bool initiate_activities = false;
 		/**
		 *
		 */
		static const bool remove_satisfied = false; // This cannot be true as otherwise incremental sat solving won't work
#ifdef __VS
        /**
         * 
         */
        static const TheoryGuidedDecisionHeuristicLevel theory_conflict_guided_decision_heuristic = TheoryGuidedDecisionHeuristicLevel::DISABLED;
        /**
         * 
         */
        static const double percentage_of_conflicts_to_add = 1.0;
        /**
         *
         */
        static const CCES conflict_clause_evaluation_strategy = CCES::SECOND_LEVEL_MINIMIZER_PLUS_LBD;
        /**
         * 
         */
        static const VARIABLE_ACTIVITY_STRATEGY initial_variable_activities = VARIABLE_ACTIVITY_STRATEGY::NONE;
#else
        /**
         * 
         */
        static constexpr TheoryGuidedDecisionHeuristicLevel theory_conflict_guided_decision_heuristic = TheoryGuidedDecisionHeuristicLevel::SATISFIED_FIRST;
        /**
         * 
         */
        static constexpr double percentage_of_conflicts_to_add = 1.0;
        /**
         *
         */
        static constexpr CCES conflict_clause_evaluation_strategy = CCES::SECOND_LEVEL_MINIMIZER_PLUS_LBD;
        /**
         * 
         */
        static constexpr VARIABLE_ACTIVITY_STRATEGY initial_variable_activities = VARIABLE_ACTIVITY_STRATEGY::NONE;
        /**
         * 
         */
        static const bool mc_sat = false;
		
		static constexpr bool validate_clauses = false;
#endif

		static constexpr bool check_for_duplicate_clauses = false;

    static constexpr bool mcsat_resolve_clause_chains = false;

    static constexpr bool mcsat_lazy_explanations = true;

    static constexpr bool mcsat_learn_lazy_explanations = false;

    static constexpr unsigned int mcsat_num_insert_assignments = 2;

    using VarScheduling = VarSchedulingDefault;

		using MCSATSettings = mcsat::MCSATSettingsFMVSNL;
    };

    struct SATSettings3 : SATSettings1
    {
		static const bool remove_satisfied = false;
	};
	
	struct SATSettingsStopAfterUnknown : SATSettings1
    {
		static const bool stop_search_after_first_unknown = true;
	};
    
    struct SATSettingsMCSAT : SATSettings1 {
        static const bool mc_sat = true;
        using VarScheduling = VarSchedulingMcsat<1>;
    };
  struct SATSettingsMCSATOC : SATSettingsMCSAT {
    static constexpr auto muduleName = "SATModule<MCSATOC>";
    using MCSATSettings = mcsat::MCSATSettingsOC;
  };
  struct SATSettingsMCSATFMVSOC : SATSettingsMCSAT {
    static constexpr auto muduleName = "SATModule<MCSATFMVSOC>";
    using MCSATSettings = mcsat::MCSATSettingsFMVSOC;
  };
	struct SATSettingsMCSATNL : SATSettingsMCSAT {
		using MCSATSettings = mcsat::MCSATSettingsNL;
    };
	struct SATSettingsMCSATFMNL : SATSettingsMCSAT {
		using MCSATSettings = mcsat::MCSATSettingsFMNL;
    };
	struct SATSettingsMCSATVSNL : SATSettingsMCSAT {
		using MCSATSettings = mcsat::MCSATSettingsVSNL;
    };
	struct SATSettingsMCSATFMVSNL : SATSettingsMCSAT {
		using MCSATSettings = mcsat::MCSATSettingsFMVSNL;
    };
}
