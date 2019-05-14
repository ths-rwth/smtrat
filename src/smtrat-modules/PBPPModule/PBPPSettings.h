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
	struct PBPPSettingsBase {
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsBase>";
		/**
		 * Example for a setting.
		 */
		static constexpr bool use_rns_transformation = false;
		static constexpr bool use_card_transformation = false;
		static constexpr bool use_mixed_transformation = false;
		static constexpr bool use_long_transformation = false;
		static constexpr bool use_short_transformation = false;
		static constexpr bool use_commander_transformation = false;
		static constexpr bool use_totalizer_transformation = false;

		// Depending on the size of the original formulation do not introduce more than a factor of 1/n
		// new formulas.
		static constexpr double MAX_NEW_RELATIVE_FORMULA_SIZE = 0.5;
		static constexpr bool USE_LIA_MIXED = false;
		static constexpr bool USE_LIA_ONLY = true;
		static constexpr bool ENCODE_IF_POSSIBLE = false;
		static constexpr bool NORMALIZE_CONSTRAINTS = false;
		static constexpr bool SPLIT_EQUALITIES = false;
	};

	struct PBPPSettingsLIAOnly : PBPPSettingsBase
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsLIAOnly>";

		// Depending on the size of the original formulation do not introduce more than a factor of 1/n
		// new formulas.
		static constexpr bool USE_LIA_ONLY = true;

	};

	struct PBPPSettings1 : PBPPSettingsBase
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettings1>";

		static constexpr bool use_card_transformation = true;
		static constexpr bool use_mixed_transformation = true;
		static constexpr bool use_long_transformation = true;
		static constexpr bool use_short_transformation = true;
		static constexpr bool use_commander_transformation = false;
		static constexpr bool use_totalizer_transformation = true;

		// Depending on the size of the original formulation do not introduce more than a factor of 1/n
		// new formulas.
		static constexpr double MAX_NEW_RELATIVE_FORMULA_SIZE = 20;
		static constexpr bool USE_LIA_MIXED = true;
		static constexpr bool USE_LIA_ONLY = false;
		static constexpr bool ENCODE_IF_POSSIBLE = true;

	};

	struct PBPPSettingsLIAOnlyWithNormalize : PBPPSettingsBase
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsLIAOnlyWithNormalize>";

		static constexpr bool USE_LIA_ONLY = true;
		static constexpr bool NORMALIZE_CONSTRAINTS = true;
	};

	struct PBPPSettingsWithNormalize : PBPPSettingsBase
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsWithNormalize>";
		/**
		 * Example for a setting.
		 */
		static constexpr bool use_card_transformation = true;
		static constexpr bool use_mixed_transformation = true;
		static constexpr bool use_long_transformation = true;
		static constexpr bool use_short_transformation = true;

		// Depending on the size of the original formulation do not introduce more than a factor of 1/n
		// new formulas.
		static constexpr double MAX_NEW_RELATIVE_FORMULA_SIZE = 20;
		static constexpr bool USE_LIA_MIXED = true;
		static constexpr bool USE_LIA_ONLY = false;
		static constexpr bool ENCODE_IF_POSSIBLE = false;
		static constexpr bool NORMALIZE_CONSTRAINTS = true;
	};

	struct PBPPSettingsCardinalityOnly20 : PBPPSettingsBase
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsCardinalityOnly20>";
		/**
		 * Example for a setting.
		 */
		static constexpr bool use_rns_transformation = false;
		static constexpr bool use_card_transformation = true;
		static constexpr bool use_mixed_transformation = false;
		static constexpr bool use_long_transformation = false;
		static constexpr bool use_short_transformation = false;
		static constexpr bool use_commander_transformation = false;

		// Depending on the size of the original formulation do not introduce more than a factor of 1/n
		// new formulas.
		static constexpr double MAX_NEW_RELATIVE_FORMULA_SIZE = 20;
		static constexpr bool USE_LIA_MIXED = true;
		static constexpr bool USE_LIA_ONLY = false;


	};

	struct PBPPSettingsCardinalityOnly05 : PBPPSettingsBase
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsCardinalityOnly05>";

		static constexpr bool use_card_transformation = true;

		// Depending on the size of the original formulation do not introduce more than a factor of 1/n
		// new formulas.
		static constexpr double MAX_NEW_RELATIVE_FORMULA_SIZE = 0.5;
		static constexpr bool USE_LIA_MIXED = true;
		static constexpr bool USE_LIA_ONLY = false;

	};

	struct PBPPSettingsFull20 : PBPPSettingsBase
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsCardinalityOnly20>";
		/**
		 * Example for a setting.
		 */
		static constexpr bool use_card_transformation = true;
		static constexpr bool use_mixed_transformation = true;
		static constexpr bool use_long_transformation = true;
		static constexpr bool use_short_transformation = true;

		// Depending on the size of the original formulation do not introduce more than a factor of 1/n
		// new formulas.
		static constexpr double MAX_NEW_RELATIVE_FORMULA_SIZE = 20;
		static constexpr bool USE_LIA_MIXED = true;
		static constexpr bool USE_LIA_ONLY = false;

	};

	struct PBPPSettingsFull05 : PBPPSettingsBase
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsCardinalityOnly05>";
		/**
		 * Example for a setting.
		 */
		static constexpr bool use_card_transformation = true;
		static constexpr bool use_mixed_transformation = true;
		static constexpr bool use_long_transformation = true;
		static constexpr bool use_short_transformation = true;

		// Depending on the size of the original formulation do not introduce more than a factor of 1/n
		// new formulas.
		static constexpr double MAX_NEW_RELATIVE_FORMULA_SIZE = 0.5;
		static constexpr bool USE_LIA_MIXED = true;
		static constexpr bool USE_LIA_ONLY = false;

	};

	struct PBPPSettingsCardinalityOnly20Normalize : PBPPSettingsBase
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsCardinalityOnly20>";

		static constexpr bool use_card_transformation = true;

		// Depending on the size of the original formulation do not introduce more than a factor of 1/n
		// new formulas.
		static constexpr double MAX_NEW_RELATIVE_FORMULA_SIZE = 20;
		static constexpr bool USE_LIA_MIXED = true;
		static constexpr bool USE_LIA_ONLY = false;
		static constexpr bool NORMALIZE_CONSTRAINTS = true;
		
	};

	struct PBPPSettingsCardinalityOnly05Normalize : PBPPSettingsBase
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsCardinalityOnly05>";

		static constexpr bool use_card_transformation = true;


		// Depending on the size of the original formulation do not introduce more than a factor of 1/n
		// new formulas.
		static constexpr double MAX_NEW_RELATIVE_FORMULA_SIZE = 0.5;
		static constexpr bool USE_LIA_MIXED = true;
		static constexpr bool USE_LIA_ONLY = false;
		static constexpr bool ENCODE_IF_POSSIBLE = false;
		static constexpr bool NORMALIZE_CONSTRAINTS = true;
	};
	
	struct PBPPSettingsWithRNS : PBPPSettingsBase
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsWithRNS>";

		static constexpr bool use_card_transformation = true;

		// Depending on the size of the original formulation do not introduce more than a factor of 1/n
		// new formulas.
		static constexpr double MAX_NEW_RELATIVE_FORMULA_SIZE = 0.5;
		static constexpr bool USE_LIA_MIXED = true;
		static constexpr bool USE_LIA_ONLY = false;
		static constexpr bool ENCODE_IF_POSSIBLE = true;

	};

	struct PBPPSettingsWithCardConstr : PBPPSettingsBase
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsWithCardConstr>";

		static constexpr bool use_card_transformation = true;

		// Depending on the size of the original formulation do not introduce more than a factor of 1/n
		// new formulas.
		static constexpr double MAX_NEW_RELATIVE_FORMULA_SIZE = 0.5;
		static constexpr bool USE_LIA_MIXED = true;
		static constexpr bool USE_LIA_ONLY = false;
		static constexpr bool ENCODE_IF_POSSIBLE = true;

	};

	struct PBPPSettingsWithMixedConstr : PBPPSettingsBase
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsWithMixedConstr>";

		static constexpr bool use_card_transformation = true;

		// Depending on the size of the original formulation do not introduce more than a factor of 1/n
		// new formulas.
		static constexpr double MAX_NEW_RELATIVE_FORMULA_SIZE = 0.5;
		static constexpr bool USE_LIA_MIXED = true;
		static constexpr bool USE_LIA_ONLY = false;
		static constexpr bool ENCODE_IF_POSSIBLE = true;

	};

	struct PBPPSettingsBasic : PBPPSettingsBase
	{
		/// Name of the Module
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsBasic>";

		static constexpr bool use_card_transformation = true;

		// Depending on the size of the original formulation do not introduce more than a factor of 1/n
		// new formulas.
		static constexpr double MAX_NEW_RELATIVE_FORMULA_SIZE = 0.5;
		static constexpr bool USE_LIA_MIXED = true;
		static constexpr bool USE_LIA_ONLY = false;
		static constexpr bool ENCODE_IF_POSSIBLE = true;

	};

	struct PBPPSettingsMaxSMT : PBPPSettingsBase {
		static constexpr auto moduleName = "PBPPModule<PBPPSettingsMaxSMT>";

		static constexpr bool use_totalizer_transformation = true;
		static constexpr bool use_card_transformation = true;

		static constexpr bool ENCODE_IF_POSSIBLE = true;

		static constexpr bool USE_LIA_MIXED = false;
		static constexpr bool USE_LIA_ONLY = false;

	};


}
