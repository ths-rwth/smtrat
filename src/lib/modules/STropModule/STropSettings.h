/**
 * @file STropSettings.h
 * @author Ömer Sali <oemer.sali@rwth-aachen.de>
 *
 * @version 2018-04-04
 * Created on 2017-09-13.
 */

#pragma once

#include "../../solver/ModuleSettings.h"

namespace smtrat
{
	enum class SeparatorType {STRICT = 0, WEAK = 1};
	
	struct STropSettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "STropModule<STropSettings1>";
		/// Type of linear separating hyperplane to search for
		static constexpr SeparatorType separatorType = SeparatorType::STRICT;
	};
}
