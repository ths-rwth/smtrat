/**
 * @file CADSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

#pragma once

#include <iostream>

#include "../../utilities/SettingsManager.h"

namespace smtrat
{
    enum class IntegerHandling {
        /// Generate a full real solution and split on non-integral assignments in this solution.
        SPLIT_SOLUTION,
        /// Split if no integral sample is available for an integer variable.
        SPLIT_LAZY,
        /// Split if a non-integral sample is available for an integer variable.
        SPLIT_EARLY,
        /// Backtrack within the sampling phase.
        BACKTRACK
    };
    inline std::ostream& operator<<(std::ostream& os, const IntegerHandling& ih) {
        switch (ih) {
            case IntegerHandling::SPLIT_SOLUTION: return os << "Split on Solution";
            case IntegerHandling::SPLIT_LAZY: return os << "Split lazy";
            case IntegerHandling::SPLIT_EARLY: return os << "Split early";
            case IntegerHandling::BACKTRACK: return os << "Backtrack";
        }
        return os;
    }
    inline std::istream& operator>>(std::istream& in, IntegerHandling& ih) {
        return in;
    }
    
	enum class MISHeuristic {
		TRIVIAL, GREEDY
	};
    
    struct CADSettings1
    {
        static constexpr IntegerHandling integer_handling = IntegerHandling::SPLIT_EARLY;
        static constexpr MISHeuristic mis_heuristic = MISHeuristic::GREEDY;
        
        static const bool dummy;
    };
}
