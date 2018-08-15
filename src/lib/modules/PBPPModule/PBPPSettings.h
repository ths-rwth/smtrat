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
	struct PBPPSettingsLIAOnly
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsLIAOnly>";
		/**
		 * Example for a setting.
		 */
		static constexpr bool use_rns_transformation = false;
		static constexpr bool use_card_transformation = false;
		static constexpr bool use_mixed_transformation = false;
		static constexpr bool use_long_transformation = false;
		static constexpr bool use_short_transformation = false;

		// Depending on the size of the original formulation do not introduce more than a factor of 1/n
		// new formulas.
		static constexpr double MAX_NEW_RELATIVE_FORMULA_SIZE = 0.5;
		static constexpr bool USE_LIA_MIXED = false;
		static constexpr bool USE_LIA_ONLY = true;
		static constexpr bool ENCODE_IF_POSSIBLE = false;

	};

	struct PBPPSettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettings1>";
		/**
		 * Example for a setting.
		 */
		static constexpr bool use_rns_transformation = false;
		static constexpr bool use_card_transformation = true;
		static constexpr bool use_mixed_transformation = false;
		static constexpr bool use_long_transformation = false;
		static constexpr bool use_short_transformation = false;

		// Depending on the size of the original formulation do not introduce more than a factor of 1/n
		// new formulas.
		static constexpr double MAX_NEW_RELATIVE_FORMULA_SIZE = 0.5;
		static constexpr bool USE_LIA_MIXED = true;
		static constexpr bool USE_LIA_ONLY = false;
		static constexpr bool ENCODE_IF_POSSIBLE = false;


	};
	
	struct PBPPSettingsWithRNS
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsWithRNS>";
		/**
		 * Example for a setting.
		 */
		static constexpr bool use_rns_transformation = false;
		static constexpr bool use_card_transformation = true;
		static constexpr bool use_mixed_transformation = false;
		static constexpr bool use_long_transformation = false;
		static constexpr bool use_short_transformation = false;
		// Depending on the size of the original formulation do not introduce more than a factor of 1/n
		// new formulas.
		static constexpr double MAX_NEW_RELATIVE_FORMULA_SIZE = 0.5;
		static constexpr bool USE_LIA_MIXED = true;
		static constexpr bool USE_LIA_ONLY = false;
		static constexpr bool ENCODE_IF_POSSIBLE = true;
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
		static constexpr bool use_long_transformation = false;
		static constexpr bool use_short_transformation = false;
		// Depending on the size of the original formulation do not introduce more than a factor of 1/n
		// new formulas.
		static constexpr double MAX_NEW_RELATIVE_FORMULA_SIZE = 0.5;
		static constexpr bool USE_LIA_MIXED = true;
		static constexpr bool USE_LIA_ONLY = false;
		static constexpr bool ENCODE_IF_POSSIBLE = true;
	};

	struct PBPPSettingsWithMixedConstr
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsWithMixedConstr>";
		/**
		 * Example for a setting.
		 */
		static constexpr bool use_rns_transformation = false;
		static constexpr bool use_card_transformation = true;
		static constexpr bool use_mixed_transformation = false;
		static constexpr bool use_long_transformation = false;
		static constexpr bool use_short_transformation = false;
		// Depending on the size of the original formulation do not introduce more than a factor of 1/n
		// new formulas.
		static constexpr double MAX_NEW_RELATIVE_FORMULA_SIZE = 0.5;
		static constexpr bool USE_LIA_MIXED = true;
		static constexpr bool USE_LIA_ONLY = false;
		static constexpr bool ENCODE_IF_POSSIBLE = true;
	};

	struct PBPPSettingsBasic
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsBasic>";
		/**
		 * Example for a setting.
		 */
		static constexpr bool use_rns_transformation = false;
		static constexpr bool use_card_transformation = true;
		static constexpr bool use_mixed_transformation = false;
		static constexpr bool use_long_transformation = false;
		static constexpr bool use_short_transformation = false;
		// Depending on the size of the original formulation do not introduce more than a factor of 1/n
		// new formulas.
		static constexpr double MAX_NEW_RELATIVE_FORMULA_SIZE = 0.5;
		static constexpr bool USE_LIA_MIXED = true;
		static constexpr bool USE_LIA_ONLY = false;
		static constexpr bool ENCODE_IF_POSSIBLE = true;
	};


}
