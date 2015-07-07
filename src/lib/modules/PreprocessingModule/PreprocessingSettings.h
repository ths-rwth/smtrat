/** 
 * @file   PreprocessingSettings.h
 * @author: Sebastian Junges
 *
 * 
 */

#pragma once

#include "../../utilities/SettingsManager.h"
#ifdef __VS
#define CONSTEXPR const
#else
#define CONSTEXPR constexpr
#endif

namespace smtrat 
{
struct PreprocessingSettings {
	static CONSTEXPR bool printChanges = false;
	/**
	 * Enables removing of redundant or obsolete factors.
	 */
	static CONSTEXPR bool removeFactors = true;
	static CONSTEXPR bool eliminateMonomialEquation = true;
	/**
	 * Enables removing of constraints that vanish within the variable bounds.
	 */
	static CONSTEXPR bool checkBounds = true;
	/**
	 * Enables removing of constraints that vanish within the variable bounds.
	 */
	static CONSTEXPR bool splitSOS = true;
    /**
	 * Enables the elimination of equations forming a substitution.
	 */
	static CONSTEXPR bool eliminateSubstitutions = true;
    /**
	 * Enables bound extraction of disjunctions of constraints with the same polynomial.
	 */
	static CONSTEXPR bool extractBounds = true;
    /**
	 * Enables removing of unbounded variables, which only occur linearly.
	 */
	static CONSTEXPR bool removeUnboundedVars = false;
	/**
     * Enables enumeration of integers with a domains of this size (0 for disabling).
     */
	static CONSTEXPR unsigned enumerate_integers_domain_size = 0;
	
	static const bool dummy;
};
}
