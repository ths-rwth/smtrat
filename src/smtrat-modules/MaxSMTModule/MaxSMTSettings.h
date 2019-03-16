/**
 * @file MaxSMTSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2019-01-25
 * Created on 2019-01-25.
 */

#pragma once

#include <smtrat-strategies/strategies/MAXSATBackendStrategy.h>

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
		static constexpr auto moduleName = "MaxSMTModule<MaxSMTSettings1>";


		static const MAXSATAlgorithm ALGORITHM = MAXSATAlgorithm::MSU3;

		using Backend = MaxSATBackendStrategy;
	};

	struct MaxSMTSettingsFuMalikIncrementalSAT : public MaxSMTSettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "MaxSMTModule<MaxSMTSettingsFuMalikIncrementalSAT>";


		static const MAXSATAlgorithm ALGORITHM = MAXSATAlgorithm::FU_MALIK_INCREMENTAL;
	};

	struct MaxSMTSettingsLinearSearchSAT : public MaxSMTSettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "MaxSMTModule<MaxSMTSettingsLinearSearchSAT>";


		static const MAXSATAlgorithm ALGORITHM = MAXSATAlgorithm::LINEAR_SEARCH;
	};

	struct MaxSMTSettingsMSU3SAT : public MaxSMTSettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "MaxSMTModule<MaxSMTSettingsMSU3SAT>";


		static const MAXSATAlgorithm ALGORITHM = MAXSATAlgorithm::MSU3;
	};
}
