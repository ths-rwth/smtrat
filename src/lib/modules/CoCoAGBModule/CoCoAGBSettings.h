/**
 * @file CoCoAGBSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2017-11-29
 * Created on 2017-11-29.
 */

#pragma once

namespace smtrat
{
	struct CoCoAGBSettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "CoCoAGBModule<CoCoAGBSettings1>";
		/**
		 * Example for a setting.
		 */
		static const bool convert_inequalities = false;
		
		static constexpr bool always_return_unknown = false;
	};
	
	struct CoCoAGBSettings2: CoCoAGBSettings1 {
		static constexpr bool always_return_unknown = true;
	}
}
