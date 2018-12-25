/**
 * @file CubeLIASettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-11-24
 * Created on 2015-11-24.
 */

#pragma once

namespace smtrat
{
	struct CubeLIASettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "CubeLIAModule<CubeLIASettings1>";
		/**
		 * 
		 */
		static const bool exclude_unsatisfiable_cube_space = false;
        
	};
}
