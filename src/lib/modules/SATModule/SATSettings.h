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
    
    enum class CCES : unsigned { SECOND_LEVEL_MINIMIZER, LITERALS_BLOCKS_DISTANCE, SECOND_LEVEL_MINIMIZER_PLUS_LBD };
    
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
        static constexpr TheoryGuidedDecisionHeuristicLevel theory_conflict_guided_decision_heuristic = TheoryGuidedDecisionHeuristicLevel::DISABLED;
        /**
         * 
         */
        static constexpr double percentage_of_conflicts_to_add = 0.0;
        /**
         *
         */
        static constexpr CCES conflict_clause_evaluation_strategy = CCES::SECOND_LEVEL_MINIMIZER_PLUS_LBD;
    };
    
    struct SATSettings2 : SATSettings1
    {
        static const bool detect_deductions = true;
    };
}

