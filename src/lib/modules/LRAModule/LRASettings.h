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
        static const bool simple_conflicts_and_propagation_on_demand = false;
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

