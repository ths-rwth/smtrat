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

		// For huge formulas it doesn't make sense to convert to bool but to stay with LIA.
		// For example x1 + ... + x100 <= 55 would introduce a lot of new formulas.
		static constexpr int max_newly_build_formulas = 30;
		static constexpr int max_literals_in_new_formula = 50;
		static constexpr bool formulate_large_formulas_as_lia = true;

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
