/**
 * Class to create a settings object for the LRAModule.
 * @file LRASettings.h
 * @author Florian Corzilius
 * @since 2014-10-01
 * @version 2014-10-01
 */

#pragma once

#include "../../datastructures/lra/TableauSettings.h"
    
namespace smtrat
{
    struct LRASettings1
    {
#ifdef __VS
		static const std::string getModuleName() { return "LRAModule<LRASettings1>"; }
#else
		static constexpr auto moduleName = "LRAModule<LRASettings1>";
#endif
        /**
         * 
         */
        static const bool simple_theory_propagation = false;
        /**
         * 
         */
        static const bool simple_conflict_search = false;
        /**
         * 
         */
        static const bool simple_conflicts_and_propagation_on_demand = true;
        /**
         * 
         */
        static const bool one_conflict_reason = false;
        /**
         * 
         */
        static const bool restore_previous_consistent_assignment = false;
        /**
         * 
         */
        static const bool branch_and_bound_early = false;
        /**
         * 
         */
        static const bool pseudo_cost_branching = false;
        /**
         * 
         */
        static const bool use_gomory_cuts = false;
        /**
         * 
         */
        static const bool use_cuts_from_proofs = false;
        /**
         * 
         */
        struct Tableau_settings : lra::TableauSettings1 {};
    };
}
