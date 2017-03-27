/**
 * @file PBPPSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2016-11-23
 * Created on 2016-11-23.
 */

#pragma once

namespace smtrat
{
	struct PBPPSettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettings1>";
		/**
		 * Example for a setting.
		 */
		static constexpr bool use_rns_transformation = false;
	};
	
	struct PBPPSettingsWithRNS
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsWithRNS>";
		/**
		 * Example for a setting.
		 */
		static constexpr bool use_rns_transformation = true;
	};
}
