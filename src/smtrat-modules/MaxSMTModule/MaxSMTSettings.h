/**
 * @file MaxSMTSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2019-01-25
 * Created on 2019-01-25.
 */

#pragma once

namespace smtrat
{
	enum MAXSATAlgorithm{
		FU_MALIK_INCREMENTAL,
		OLL,
		MSU3,
		LINEAR_SEARCH
	};

	struct MaxSMTSettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "MaxSMTModule<MaxSMTSettingsMSU3>";


		static const MAXSATAlgorithm ALGORITHM = MAXSATAlgorithm::MSU3;
	};

	struct MaxSMTSettingsFuMalikIncremental
	{
		/// Name of the Module
		static constexpr auto moduleName = "MaxSMTModule<MaxSMTSettingsFuMalikIncremental>";


		static const MAXSATAlgorithm ALGORITHM = MAXSATAlgorithm::FU_MALIK_INCREMENTAL;
	};

	struct MaxSMTSettingsLinearSearch
	{
		/// Name of the Module
		static constexpr auto moduleName = "MaxSMTModule<MaxSMTSettingsLinearSearch>";


		static const MAXSATAlgorithm ALGORITHM = MAXSATAlgorithm::LINEAR_SEARCH;
	};

	struct MaxSMTSettingsMSU3
	{
		/// Name of the Module
		static constexpr auto moduleName = "MaxSMTModule<MaxSMTSettingsMSU3>";


		static const MAXSATAlgorithm ALGORITHM = MAXSATAlgorithm::MSU3;
	};
}
