/**
 * @file CSplitSettings.h
 * @author Ömer Sali <oemer.sali@rwth-aachen.de>
 *
 * @version 2018-04-04
 * Created on 2017-11-01.
 */

#pragma once

#include "../../solver/ModuleSettings.h"

namespace smtrat
{
	struct CSplitSettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "CSplitModule<CSplitSettings1>";
		/// Limit size for the domain of variables that need to be expanded
		static constexpr size_t maxDomainSize = 32;
		/// Base number 2 <= expansionBase <= maxDomainSize for the expansion
		static constexpr size_t expansionBase = 32;
		/// Common denominator for the discretization of rational variables
		static constexpr size_t discrDenom = 16;
		/// Maximum number of iterations
		static constexpr size_t maxIter = 400;
		/// Radius of initial domain
		static constexpr size_t initialRadius = 1;
		/// Threshold radius to
		///   - start exponential bloating of vaiables used for case splits
		///   - activate full domains of variables not used for case splits
		static constexpr size_t thresholdRadius = 5;
		///
		static constexpr size_t radiusIncrement = 1;
		///
		static constexpr size_t maximalRadius = 300;
		/// Maximal number of bounds to bloat in one iteration
		static constexpr size_t maxBloatedDomains = 5;
	};
}
