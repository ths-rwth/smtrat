/**
 * @file AbstractSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2018-07-12
 * Created on 2018-07-12.
 */

#pragma once

namespace smtrat
{
	struct AbstractSettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "AbstractModule<AbstractSettings1>";
		/**
		 * Example for a setting.
		 */
		static const bool example_setting = true;
	};
}
