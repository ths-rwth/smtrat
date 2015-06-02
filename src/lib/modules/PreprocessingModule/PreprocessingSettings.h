/** 
 * @file   PreprocessingSettings.h
 * @author: Sebastian Junges
 *
 * 
 */

#pragma once

#include "../../utilities/SettingsManager.h"

namespace smtrat 
{
struct PreprocessingSettings {
	/**
	 * Enables removing of redundant or obsolete factors.
	 */
	static constexpr bool removeFactors = true;
	/**
	 * Enables removing of constraints that vanish within the variable bounds.
	 */
	static constexpr bool checkBounds = true;
	/**
	 * Enables removing of constraints that vanish within the variable bounds.
	 */
	static constexpr bool splitSOS = true;
    /**
	 * Enables the elimination of equations forming a substitution.
	 */
	static constexpr bool eliminateSubstitutions = false;
	
	static const bool dummy;
};
}
