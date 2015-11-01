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
#ifdef __VS
		#define CONSTEXPR const
		static const std::string getModuleName() { return "SATModule<SATSettings1>"; }
#else
		#define CONSTEXPR constexpr
		static constexpr auto moduleName = "SATModule<SATSettings1>";
#endif
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
        static const bool check_if_all_clauses_are_satisfied = false;
        /**
         * 
         */
		static CONSTEXPR TheoryGuidedDecisionHeuristicLevel theory_conflict_guided_decision_heuristic = TheoryGuidedDecisionHeuristicLevel::DISABLED;
        /**
         * 
         */
#ifdef __VS
		static const double percentage_of_conflicts_to_add;
#else
		static CONSTEXPR double percentage_of_conflicts_to_add = 1.0;
#endif
        /**
         *
         */
		static CONSTEXPR CCES conflict_clause_evaluation_strategy = CCES::SECOND_LEVEL_MINIMIZER_PLUS_LBD;
		/**
		 *
		 */
		static const bool remove_satisfied = false;
    };

#ifdef __VS
	const double SATSettings1::percentage_of_conflicts_to_add = 1.0;
#endif
}
