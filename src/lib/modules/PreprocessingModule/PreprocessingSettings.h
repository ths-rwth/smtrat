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
#ifdef __VS
	/**
	 * Enables removing of redundant or obsolete factors.
	 */
	static const bool removeFactors = true;
	/**
	 * Enables removing of constraints that vanish within the variable bounds.
	 */
	static const bool checkBounds = true;
	/**
	 * Enables removing of constraints that vanish within the variable bounds.
	 */
	static const bool splitSOS = true;
    /**
	 * Enables the elimination of equations forming a substitution.
	 */
	static const bool eliminateSubstitutions = true;
    /**
	 * Enables bound extraction of disjunctions of constraints with the same polynomial.
	 */
	static const bool extractBounds = true;
    /**
	 * Enables removing of unbounded variables, which only occur linearly.
	 */
	static const bool removeUnboundedVars = false;
#else
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
	static constexpr bool eliminateSubstitutions = true;
    /**
	 * Enables bound extraction of disjunctions of constraints with the same polynomial.
	 */
	static constexpr bool extractBounds = true;
    /**
	 * Enables removing of unbounded variables, which only occur linearly.
	 */
	static constexpr bool removeUnboundedVars = false;
#endif	
	static const bool dummy;
};
}
