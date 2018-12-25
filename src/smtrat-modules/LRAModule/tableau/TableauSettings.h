/**
 * Class to create a settings object for the Tableau.
 * @file TableauSettings.h
 * @author Florian Corzilius
 * @since 2014-10-01
 * @version 2014-10-01
 */

#pragma once

namespace smtrat
{   
    namespace lra
    {
        
        enum class NBCS : unsigned { LESS_BOUNDED_VARIABLES, LESS_COLUMN_ENTRIES };
    
        struct TableauSettings1
        {
            /**
             * 
             */
            static const bool use_pivoting_strategy = true;
            /**
             * 
             */
            static const bool use_refinement = true;
            /**
             * 
             */
            static const bool prefer_equations = false;
            /**
             * 
             */
            static const bool pivot_into_local_conflict = true;
            /**
             * 
             */
            static const bool use_activity_based_pivot_strategy = false;
            /**
             * 
             */
            static const bool use_theta_based_pivot_strategy = false;
            /**
             * 
             */
            static const bool introduce_new_constraint_in_refinement = false;
            /**
             * 
             */
            static const bool omit_division = true;
            /**
             *
             */
            static constexpr NBCS nonbasic_var_choice_strategy = NBCS::LESS_COLUMN_ENTRIES;
        };
        
        struct TableauSettings2 : TableauSettings1
        {
            static const bool omit_division = false;
        };
        
        struct TableauSettings3 : TableauSettings1
        {
            static const bool use_refinement = false;
        };
    }
}
