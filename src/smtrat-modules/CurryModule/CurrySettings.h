/**
 * @file CurrySettings.h
 * @author Henrich Lauko <xlauko@mail.muni.cz>
 * @author Dominika Krejci <dominika.krejci@rwth-aachen.de>
 *
 * @version 2018-11-18
 * Created on 2018-11-18.
 */

#pragma once

namespace smtrat
{
	struct CurrySettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "CurryModule<CurrySettings1>";
		/**
		 * Example for a setting.
		 */
		static const bool example_setting = true;
	};
}
