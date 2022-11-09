/**
 * @file NewFMPlexSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2022-10-07
 * Created on 2022-10-07.
 */

#pragma once

namespace smtrat
{
	enum EQ_Handling {
		GAUSSIAN
	};

	struct NewFMPlexSettings
	{
		/// Name of the Module
		static constexpr auto moduleName = "NewFMPlexModule<NewFMPlexSettings1>";
		/**
		 * Example for a setting.
		 */
		static constexpr bool incremental = false;
		static constexpr bool use_backtracking = false;
		static constexpr EQ_Handling eq_handling = EQ_Handling::GAUSSIAN;
	};
}
