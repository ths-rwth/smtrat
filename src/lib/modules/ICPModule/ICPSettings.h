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
    enum class SplittingHeuristic : unsigned { IMPACT, UNSATISFIABILITY, SATISFIABILITY };
            
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
        static constexpr double contraction_threshold_nra = 0.01;
        /**
         * 
         */
        static constexpr double default_splitting_size_nia = 16;
        /**
         * 
         */
        static constexpr double default_splitting_size_nra = 1000;
        /**
         * 
         */
        static constexpr SplittingHeuristic splitting_heuristic_nia = SplittingHeuristic::IMPACT;
        /**
         * 
         */
        static constexpr SplittingHeuristic splitting_heuristic_nra = SplittingHeuristic::IMPACT;
        /**
         * 
         */
        static constexpr size_t number_of_reusages_after_target_diameter_reached = 1;
        
    };
}
