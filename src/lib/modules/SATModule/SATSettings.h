/**
 * Class to create a settings object for the SATModule.
 * @file SATSettings.h
 * @author Florian Corzilius
 * @since 2014-10-02
 * @version 2014-10-02
 */

#pragma once
    
namespace smtrat
{
    enum class TheoryGuidedDecisionHeuristicLevel : unsigned { CONFLICT_FIRST, NON_SATISFIED_FIRST, DISABLED };
    
    struct SATSettings1
    {
        /**
         * 
         */
        static const bool allow_theory_propagation = true;
        /**
         * 
         */
        static const bool detect_deductions = false;
        /**
         * 
         */
        static const bool try_full_lazy_call_first = false;
        /**
         * 
         */
        static const bool apply_valid_substitutions = false;
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
#ifdef __VS
        static const TheoryGuidedDecisionHeuristicLevel theory_conflict_guided_decision_heuristic = TheoryGuidedDecisionHeuristicLevel::DISABLED;
#else
        static constexpr TheoryGuidedDecisionHeuristicLevel theory_conflict_guided_decision_heuristic = TheoryGuidedDecisionHeuristicLevel::DISABLED;
#endif
    };
    
    struct SATSettings2 : SATSettings1
    {
        static const bool detect_deductions = true;
    };

    struct SATSettings3 : SATSettings1
    {
        static const bool compute_propagated_lemmas = false;
        static const bool find_all_dependent_variables = false;
		static const bool remove_satisfied = false;
	};
}

