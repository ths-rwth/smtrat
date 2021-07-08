/**
 * @file NewCoveringSettings.h
 * @author Philip Kroll <Philip.Kroll@rwth-aachen.de>
 *
 * @version 2021-07-08
 * Created on 2021-07-08.
 */

#pragma once

namespace smtrat
{
	struct NewCoveringSettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "NewCoveringModule<NewCoveringSettings1>";
		/**
		 * Example for a setting.
		 */
		static const bool example_setting = true;
	};
}
