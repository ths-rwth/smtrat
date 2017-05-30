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
		static constexpr bool use_card_transformation = false;
		static constexpr bool use_mixed_transformation = false;
		static constexpr bool use_basic_transformation = false;

	};
	
	struct PBPPSettingsWithRNS
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsWithRNS>";
		/**
		 * Example for a setting.
		 */
		static constexpr bool use_rns_transformation = true;
		static constexpr bool use_card_transformation = false;
		static constexpr bool use_mixed_transformation = false;
		static constexpr bool use_basic_transformation = false;
	};

	struct PBPPSettingsWithCardConstr
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsWithCardConstr>";
		/**
		 * Example for a setting.
		 */
		static constexpr bool use_rns_transformation = false;
		static constexpr bool use_card_transformation = true;
		static constexpr bool use_mixed_transformation = false;
		static constexpr bool use_basic_transformation = false;
	};

	struct PBPPSettingsWithMixedConstr
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsWithMixedConstr>";
		/**
		 * Example for a setting.
		 */
		static constexpr bool use_rns_transformation = false;
		static constexpr bool use_card_transformation = false;
		static constexpr bool use_mixed_transformation = true;
		static constexpr bool use_basic_transformation = false;
	};

	struct PBPPSettingsBasic
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsBasic>";
		/**
		 * Example for a setting.
		 */
		static constexpr bool use_rns_transformation = false;
		static constexpr bool use_card_transformation = false;
		static constexpr bool use_mixed_transformation = false;
		static constexpr bool use_basic_transformation = true;
	};


}
