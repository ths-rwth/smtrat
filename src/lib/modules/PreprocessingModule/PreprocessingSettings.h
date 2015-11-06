/** 
 * @file   PreprocessingSettings.h
 * @author: Sebastian Junges
 *
 * 
 */

#pragma once

#include "../../solver/ModuleSettings.h"
#include "../../utilities/SettingsManager.h"

namespace smtrat 
{
struct PreprocessingSettings1 : ModuleSettings {
	static constexpr auto moduleName = "PreprocessingModule<PreprocessingSettings1>";
	static constexpr bool printChanges = false;
	/**
	 * Enables removing of redundant or obsolete factors.
	 */
	static constexpr bool removeFactors = true;
	static constexpr bool eliminateMonomialEquation = true;
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
	static constexpr bool eliminateSubstitutions = true;
    /**
	 * Enables bound extraction of disjunctions of constraints with the same polynomial.
	 */
	static constexpr bool extractBounds = true;
    /**
	 * Enables removing of unbounded variables, which only occur linearly.
	 */
	static constexpr bool removeUnboundedVars = false;
	/**
     * Enables enumeration of integers with a domains of this size (0 for disabling).
     */
	static constexpr unsigned enumerate_integers_domain_size = 0;
	
	static const bool dummy;
};
}
