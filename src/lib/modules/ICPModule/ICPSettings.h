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
#ifdef __VS
		static const std::string getModuleName() { return "ICPModule<ICPSettings1>"; }
		/**
		* 
		*/
		static const double getTarget_diameter_nia() { return 0.1; }
		/**
		*
		*/
		static const double getTarget_diameter_nra() { return 0.01; }
		/**
		*
		*/
		static const double getContraction_threshold_nia() { return 0.01; }
		/**
		*
		*/
		static const double getContraction_threshold_nra() { return 0.001; } // Because we currently cannot change the settings within one strategy
#else
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
#endif
		/**
		*
		*/
		static CONSTEXPR int default_splitting_size_nia = 16;
		/**
		*
		*/
		static CONSTEXPR int default_splitting_size_nra = 1000; // Because we currently cannot change the settings within one strategy
        /**
         * 
         */
		static CONSTEXPR SplittingHeuristic splitting_heuristic_nia = SplittingHeuristic::SIZE;
        /**
         * 
         */
		static CONSTEXPR SplittingHeuristic splitting_heuristic_nra = SplittingHeuristic::SIZE; // Because we currently cannot change the settings within one strategy
        /**
         * 
         */
		static CONSTEXPR size_t number_of_reusages_after_target_diameter_reached = 1;
        /**
         * 
         */
		static CONSTEXPR bool first_split_to_bounded_intervals_without_zero = true;
        /**
         * 
         */
		static CONSTEXPR bool use_lramodules_splitting_decisions = false;
        /**
         * 
         */
		static CONSTEXPR bool use_backends_splitting_decisions = false;
        /**
         * 
         */
		static CONSTEXPR bool prolong_contraction = true;
        /**
         * 
         */
		static CONSTEXPR bool original_polynomial_contraction = false;
        /**
         * 
         */
		static CONSTEXPR bool use_propagation = true;
        
    };
}
