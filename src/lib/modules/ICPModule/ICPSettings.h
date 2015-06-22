/**
 * Class to create a settings object for the ICPModule.
 * @file ICPSettings.h
 * @author Florian Corzilius
 * @since 2014-10-02
 * @version 2014-10-02
 */

#pragma once
    
#include "../../config.h"

namespace smtrat
{
    enum class SplittingHeuristic : unsigned { SIZE, UNSATISFIABILITY, SATISFIABILITY };
            
    struct ICPSettings1
    {
        /**
         * 
         */
        static constexpr double target_diameter_nia = 0.1;
        /**
         * 
         */
        static constexpr double target_diameter_nra = 0.1;
        /**
         * 
         */
        static constexpr double contraction_threshold_nia = 0.01;
        /**
         * 
         */
        static constexpr double contraction_threshold_nra = 0.01; // Because we currently cannot change the settings within one strategy
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
        static constexpr bool use_lramodules_splitting_decisions = false;
        /**
         * 
         */
        static constexpr bool use_backends_splitting_decisions = true;
        
    };
}
