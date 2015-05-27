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
        static const bool handle_theory_conflict_as_lemma = true;
        /**
         * 
         */
        static const bool use_restarts = true;
        /**
         * 
         */
        static const bool stop_search_after_first_unknown = true; //TODO: repair this when deactivated (see qf_lra/bugs/bug_sat_dont_stop_by_first_unknown.smt2)
        /**
         * 
         */
        static const bool formula_guided_decision_heuristic = false;
    };
    
    struct SATSettings2 : SATSettings1
    {
        static const bool detect_deductions = true;
    };
}

