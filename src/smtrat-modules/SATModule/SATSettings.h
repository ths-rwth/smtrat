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
    
namespace smtrat
{
    enum class CCES : unsigned { SECOND_LEVEL_MINIMIZER, LITERALS_BLOCKS_DISTANCE, SECOND_LEVEL_MINIMIZER_PLUS_LBD };
    
    enum class VARIABLE_ACTIVITY_STRATEGY : unsigned { NONE, MIN_COMPLEXITY_MAX_OCCURRENCES };

    enum class MCSAT_BOOLEAN_DOMAIN_PROPAGATION : unsigned { NONE, PARTIAL_CONFLICT, PARTIAL, FULL};
    
    struct SATSettings1
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
		// TODO this settings and the order_heap related code can be removed as the VarScheduler implementation turns out to be working:
        static constexpr TheoryGuidedDecisionHeuristicLevel theory_conflict_guided_decision_heuristic = TheoryGuidedDecisionHeuristicLevel::DISABLED;
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

		static constexpr bool mcsat_learn_lazy_explanations = false;

		static constexpr unsigned int mcsat_num_insert_assignments = 1;

		static constexpr MCSAT_BOOLEAN_DOMAIN_PROPAGATION mcsat_boolean_domain_propagation = MCSAT_BOOLEAN_DOMAIN_PROPAGATION::FULL;

    static constexpr bool mcsat_backjump_decide = true;

		static constexpr bool use_new_var_scheduler = true;
		using VarScheduler = VarSchedulerSMTTheoryGuided<TheoryGuidedDecisionHeuristicLevel::SATISFIED_FIRST>;

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
        // static const bool check_active_literal_occurrences = true;
        // needed for variable scheduling to work:
        static constexpr TheoryGuidedDecisionHeuristicLevel theory_conflict_guided_decision_heuristic = TheoryGuidedDecisionHeuristicLevel::DISABLED;
		    static constexpr bool use_new_var_scheduler = true;
        // using VarScheduler = VarSchedulerMcsatBooleanFirst<mcsat::VariableOrdering::FeatureBased>;
        using VarScheduler = VarSchedulerMcsatTheoryFirst<TheoryVarSchedulerStatic<mcsat::VariableOrdering::FeatureBasedBrown>>;
        //using VarScheduler = VarSchedulerMcsatUnivariateClausesOnly<TheoryVarSchedulerStatic<mcsat::VariableOrdering::FeatureBased>,false>;
        // using VarScheduler = VarSchedulerMcsatTheoryFirst<VarSchedulerMinisat>;
        // using VarScheduler = VarSchedulerMcsatUnivariateConstraintsOnly<1, mcsat::VariableOrdering::FeatureBased>;
        // using VarScheduler = VarSchedulerMcsatActivityPreferTheory<mcsat::VariableOrdering::FeatureBased>;

        // uniform (resp Boolean and theory vars) decision heuristic
        // Note: mcsat_backjump_decide needs to be activated, otherwise we run into termination problems!
        // using VarScheduler = VarSchedulerMinisat;
        // using VarScheduler = VarSchedulerFixedRandom;
    };
struct SATSettingsMCSATOC : SATSettingsMCSAT {
    static constexpr auto muduleName = "SATModule<MCSATOC>";
    using MCSATSettings = mcsat::MCSATSettingsOC;
};
struct SATSettingsMCSATOCNew : SATSettingsMCSAT {
    static constexpr auto muduleName = "SATModule<MCSATOCNew>";
    using MCSATSettings = mcsat::MCSATSettingsOCNew;
};
struct SATSettingsMCSATOCNNASC : SATSettingsMCSAT {
	static constexpr auto muduleName = "SATModule<MCSATOCNNASC>";
	using MCSATSettings = mcsat::MCSATSettingsOCNNASC;
};
struct SATSettingsMCSATOCNNDSC : SATSettingsMCSAT {
    static constexpr auto muduleName = "SATModule<MCSATOCNNDSC>";
    using MCSATSettings = mcsat::MCSATSettingsOCNNDSC;
};
struct SATSettingsMCSATOCLWH11 : SATSettingsMCSAT {
	static constexpr auto muduleName = "SATModule<MCSATOCLWH11>";
	using MCSATSettings = mcsat::MCSATSettingsOCLWH11;
};
struct SATSettingsMCSATOCLWH12 : SATSettingsMCSAT {
	static constexpr auto muduleName = "SATModule<MCSATOCLWH12>";
	using MCSATSettings = mcsat::MCSATSettingsOCLWH12;
};
struct SATSettingsMCSATOCLWH13 : SATSettingsMCSAT {
	static constexpr auto muduleName = "SATModule<MCSATOCLWH13>";
	using MCSATSettings = mcsat::MCSATSettingsOCLWH13;
};
struct SATSettingsMCSATOCLWH21 : SATSettingsMCSAT {
	static constexpr auto muduleName = "SATModule<MCSATOCLWH21>";
	using MCSATSettings = mcsat::MCSATSettingsOCLWH21;
};
struct SATSettingsMCSATOCLWH22 : SATSettingsMCSAT {
	static constexpr auto muduleName = "SATModule<MCSATOCLWH22>";
	using MCSATSettings = mcsat::MCSATSettingsOCLWH22;
};
struct SATSettingsMCSATOCLWH23 : SATSettingsMCSAT {
	static constexpr auto muduleName = "SATModule<MCSATOCLWH23>";
	using MCSATSettings = mcsat::MCSATSettingsOCLWH23;
};
struct SATSettingsMCSATOCLWH31 : SATSettingsMCSAT {
	static constexpr auto muduleName = "SATModule<MCSATOCLWH31>";
	using MCSATSettings = mcsat::MCSATSettingsOCLWH31;
};
struct SATSettingsMCSATOCLWH32 : SATSettingsMCSAT {
	static constexpr auto muduleName = "SATModule<MCSATOCLWH32>";
	using MCSATSettings = mcsat::MCSATSettingsOCLWH32;
};
struct SATSettingsMCSATOCLWH33 : SATSettingsMCSAT {
	static constexpr auto muduleName = "SATModule<MCSATOCLWH33>";
	using MCSATSettings = mcsat::MCSATSettingsOCLWH33;
};
struct SATSettingsMCSATFMICPVSOCLWH13 : SATSettingsMCSAT {
	static constexpr auto muduleName = "SATModule<MCSATFMICPVSOCLWH13>";
	using MCSATSettings = mcsat::MCSATSettingsFMICPVSOCLWH13;
};
struct SATSettingsMCSATFMICPVSOCPARALLEL : SATSettingsMCSAT {
    static constexpr auto muduleName = "SATModule<MCSATFMICPVSOCPARALLEL>";
    using MCSATSettings = mcsat::MCSATSettingsFMICPVSOCPARALLEL;
};
struct SATSettingsMCSATOCPARALLEL : SATSettingsMCSAT {
    static constexpr auto muduleName = "SATModule<MCSATOCPARALLEL>";
    using MCSATSettings = mcsat::MCSATSettingsOCPARALLEL;
};
  struct SATSettingsMCSATFMVSOC : SATSettingsMCSAT {
    static constexpr auto muduleName = "SATModule<MCSATFMVSOC>";
    using MCSATSettings = mcsat::MCSATSettingsFMVSOC;
  };
  struct SATSettingsMCSATFMICPVSOC : SATSettingsMCSAT {
    static constexpr auto muduleName = "SATModule<MCSATFMICPVSOC>";
    using MCSATSettings = mcsat::MCSATSettingsFMICPVSOC;
  };
	struct SATSettingsMCSATNL : SATSettingsMCSAT {
		static constexpr auto moduleName = "SATModule<MCSATNL>";
		using MCSATSettings = mcsat::MCSATSettingsNL;
    };
	struct SATSettingsMCSATFMNL : SATSettingsMCSAT {
		static constexpr auto moduleName = "SATModule<MCSATFMNL>";
		using MCSATSettings = mcsat::MCSATSettingsFMNL;
    };
	struct SATSettingsMCSATVSNL : SATSettingsMCSAT {
		static constexpr auto moduleName = "SATModule<MCSATVSNL>";
		using MCSATSettings = mcsat::MCSATSettingsVSNL;
    };
	struct SATSettingsMCSATFMVSNL : SATSettingsMCSAT {
		static constexpr auto moduleName = "SATModule<MCSATFMVSNL>";
		using MCSATSettings = mcsat::MCSATSettingsFMVSNL;
    };
	struct SATSettingsMCSATICPNL : SATSettingsMCSAT {
		static constexpr auto moduleName = "SATModule<MCSATICPNL>";
		using MCSATSettings = mcsat::MCSATSettingsICPNL;
    };

	struct BaseSATSettings_MCSAT : SATSettings1 {
		static constexpr bool mc_sat = true;
		static constexpr TheoryGuidedDecisionHeuristicLevel theory_conflict_guided_decision_heuristic = TheoryGuidedDecisionHeuristicLevel::DISABLED;
		static constexpr bool use_new_var_scheduler = true;
	};
	struct SATSettings_MCSAT_AF_FMOCNL_TF : BaseSATSettings_MCSAT {
		static constexpr auto moduleName = "SATModule<MCSATAFFMOCNLTF>";
		using MCSATSettings = mcsat::MCSAT_AF_FMOCNL;
		using VarScheduler = VarSchedulerMcsatTheoryFirst<TheoryVarSchedulerStatic<mcsat::VariableOrdering::FeatureBased>>;
	};

	struct SATSettings_MCSAT_AF_NL_TF : BaseSATSettings_MCSAT {
		static constexpr auto moduleName = "SATModule<MCSATAFNLTF>";
		using MCSATSettings = mcsat::MCSAT_AF_NL;
		using VarScheduler = VarSchedulerMcsatTheoryFirst<TheoryVarSchedulerStatic<mcsat::VariableOrdering::FeatureBased>>;
	};
	struct SATSettings_MCSAT_AF_OCNL_TF : BaseSATSettings_MCSAT {
		static constexpr auto moduleName = "SATModule<MCSATAFOCNLTF>";
		using MCSATSettings = mcsat::MCSAT_AF_OCNL;
		using VarScheduler = VarSchedulerMcsatTheoryFirst<TheoryVarSchedulerStatic<mcsat::VariableOrdering::FeatureBased>>;
	};
	struct SATSettings_MCSAT_AF_FMICPOCNL_TF : BaseSATSettings_MCSAT {
		static constexpr auto moduleName = "SATModule<MCSATAFFMICPOCNLTF>";
		using MCSATSettings = mcsat::MCSAT_AF_FMICPOCNL;
		using VarScheduler = VarSchedulerMcsatTheoryFirst<TheoryVarSchedulerStatic<mcsat::VariableOrdering::FeatureBased>>;
	};
	struct SATSettings_MCSAT_AF_FMICPVSOCNL_TF : BaseSATSettings_MCSAT {
		static constexpr auto moduleName = "SATModule<MCSATAFFMICPVSOCNLTF>";
		using MCSATSettings = mcsat::MCSAT_AF_FMICPVSOCNL;
		using VarScheduler = VarSchedulerMcsatTheoryFirst<TheoryVarSchedulerStatic<mcsat::VariableOrdering::FeatureBased>>;
	};
	struct SATSettings_MCSAT_AF_FMVSOCNL_TF : BaseSATSettings_MCSAT {
		static constexpr auto moduleName = "SATModule<MCSATAFFMVSOCNLTF>";
		using MCSATSettings = mcsat::MCSAT_AF_FMVSOCNL;
		using VarScheduler = VarSchedulerMcsatTheoryFirst<TheoryVarSchedulerStatic<mcsat::VariableOrdering::FeatureBased>>;
	};

	struct SATSettings_MCSAT_SMT_FMOCNL_TF : BaseSATSettings_MCSAT {
		static constexpr auto moduleName = "SATModule<MCSATSMTFMOCNLTF>";
		using MCSATSettings = mcsat::MCSAT_SMT_FMOCNL;
		using VarScheduler = VarSchedulerMcsatTheoryFirst<TheoryVarSchedulerStatic<mcsat::VariableOrdering::FeatureBased>>;
	};

	struct SATSettings_MCSAT_AF_FMOCNL_BF : BaseSATSettings_MCSAT {
		static constexpr auto moduleName = "SATModule<MCSATAFFMOCNLBF>";
		using MCSATSettings = mcsat::MCSAT_AF_FMOCNL;
		using VarScheduler = VarSchedulerMcsatBooleanFirst<mcsat::VariableOrdering::FeatureBased>;
	};
	struct SATSettings_MCSAT_AF_FMOCNL_RND : BaseSATSettings_MCSAT {
		static constexpr auto moduleName = "SATModule<MCSATAFFMOCNLRND>";
		using MCSATSettings = mcsat::MCSAT_AF_FMOCNL;
		using VarScheduler = VarSchedulerFixedRandom;
	};
	struct SATSettings_MCSAT_AF_FMOCNL_UNIFORM : BaseSATSettings_MCSAT {
		static constexpr auto moduleName = "SATModule<MCSATAFFMOCNLUNIFORM>";
		using MCSATSettings = mcsat::MCSAT_AF_FMOCNL;
		using VarScheduler = VarSchedulerMinisat;
	};
	struct SATSettings_MCSAT_AF_FMOCNL_UV : BaseSATSettings_MCSAT {
		static constexpr auto moduleName = "SATModule<MCSATAFFMOCNLUV>";
		using MCSATSettings = mcsat::MCSAT_AF_FMOCNL;
		using VarScheduler = VarSchedulerMcsatUnivariateConstraintsOnly<1, mcsat::VariableOrdering::FeatureBased>;
	};
	struct SATSettings_MCSAT_AF_FMOCNL_UVactive : BaseSATSettings_MCSAT {
		static constexpr auto moduleName = "SATModule<MCSATAFFMOCNLUVactive>";
		using MCSATSettings = mcsat::MCSAT_AF_FMOCNL;
		using VarScheduler = VarSchedulerMcsatUnivariateConstraintsOnly<1, mcsat::VariableOrdering::FeatureBased>;
		static constexpr bool check_active_literal_occurrences = true;
	};
	struct SATSettings_MCSAT_AF_FMOCNL_NLSAT : BaseSATSettings_MCSAT {
		static constexpr auto moduleName = "SATModule<MCSATAFFMOCNLNLSAT>";
		using MCSATSettings = mcsat::MCSAT_AF_FMOCNL;
		using VarScheduler = VarSchedulerMcsatUnivariateClausesOnly<TheoryVarSchedulerStatic<mcsat::VariableOrdering::FeatureBased>,false>;
	};
	struct SATSettings_MCSAT_AF_FMOCNL_TFDYN : BaseSATSettings_MCSAT {
		static constexpr auto moduleName = "SATModule<MCSATAFFMOCNLTFDYN>";
		using MCSATSettings = mcsat::MCSAT_AF_FMOCNL;
		using VarScheduler = VarSchedulerMcsatTheoryFirst<VarSchedulerMinisat>;
	};
	struct SATSettings_MCSAT_AF_FMOCNL_UNIFORMTF : BaseSATSettings_MCSAT {
		static constexpr auto moduleName = "SATModule<MCSATAFFMOCNLUNIFORMTF>";
		using MCSATSettings = mcsat::MCSAT_AF_FMOCNL;
		using VarScheduler = VarSchedulerMcsatActivityPreferTheory<mcsat::VariableOrdering::FeatureBased>;
	};
}
