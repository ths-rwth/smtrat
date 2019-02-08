/**
 * Class to create a settings object for the ICPModule.
 * @file ICPSettings.h
 * @author Florian Corzilius
 * @since 2014-10-02
 * @version 2014-10-02
 */

#pragma once
    
#include <smtrat-common/smtrat-common.h>

namespace smtrat
{
    enum class SplittingHeuristic : unsigned { SIZE, UNSATISFIABILITY, SATISFIABILITY };
            
    struct ICPSettings1
    {
		static constexpr auto moduleName = "ICPModule<ICPSettings1>";
        /**
         * 
         */
        static constexpr double target_diameter_nia = 0.1;
        /**
         * 
         */
        static constexpr double target_diameter_nra = 0.01;
        /**
         * 
         */
        static constexpr double contraction_threshold_nia = 0.01;
        /**
         * 
         */
        static constexpr double contraction_threshold_nra = 0.001; // Because we currently cannot change the settings within one strategy
        /**
         * 
         */
        static constexpr double default_splitting_size_nia = 16;
        /**
         * 
         */
        static constexpr double default_splitting_size_nra = 1000; // Because we currently cannot change the settings within one strategy
        /**
         * 
         */
        static constexpr SplittingHeuristic splitting_heuristic_nia = SplittingHeuristic::SIZE;
        /**
         * 
         */
        static constexpr SplittingHeuristic splitting_heuristic_nra = SplittingHeuristic::SIZE; // Because we currently cannot change the settings within one strategy
        /**
         * 
         */
        static constexpr size_t number_of_reusages_after_target_diameter_reached = 1;
        /**
         * 
         */
        static constexpr bool first_split_to_bounded_intervals_without_zero = true;
        /**
         * 
         */
        static constexpr bool prolong_contraction = true;
        /**
         * 
         */
        static constexpr bool original_polynomial_contraction = false;
        /**
         * 
         */
        static constexpr bool use_propagation = true;
        /**
         * 
         */
        static constexpr bool split_by_division_with_zero = true;
        /**
         * 
         */
        static constexpr bool just_contraction = false;
        
    };
    
    struct ICPSettings2 : ICPSettings1
    {
		static constexpr auto moduleName = "ICPModule<ICPSettings2>";
        static constexpr double default_splitting_size_nia = 100;
    };
    
    struct ICPSettings3 : ICPSettings1
    {
		static constexpr auto moduleName = "ICPModule<ICPSettings3>";
        static constexpr bool split_by_division_with_zero = false;
    };
    
    struct ICPSettings4 : ICPSettings1
    {
		static constexpr auto moduleName = "ICPModule<ICPSettings4>";
        static constexpr bool just_contraction = true;
    };
}
