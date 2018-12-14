/**
 * @file UnionFindSettings.h
 * @author Henrich Lauko <xlauko@mail.muni.cz>
 * @author Dominika Krejci <dominika.krejci@rwth-aachen.de>
 *
 * @version 2018-11-18
 * Created on 2018-11-18.
 */

#pragma once

namespace smtrat
{
	struct UnionFindSettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "UnionFindModule<UnionFindSettings1>";
		/**
		 * Example for a setting.
		 */
		static const bool example_setting = true;
	};
}
