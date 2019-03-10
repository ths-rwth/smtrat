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

	struct MaxSMTSettingsFuMalikIncremental
	{
		/// Name of the Module
		static constexpr auto moduleName = "MaxSMTModule<MaxSMTSettings1>";


		static const MAXSATAlgorithm ALGORITHM = MAXSATAlgorithm::FU_MALIK_INCREMENTAL;
	};

	struct MaxSMTSettingsLinearSearch
	{
		/// Name of the Module
		static constexpr auto moduleName = "MaxSMTModule<MaxSMTSettings1>";


		static const MAXSATAlgorithm ALGORITHM = MAXSATAlgorithm::LINEAR_SEARCH;
	};
}
