/**
 * @file ICESettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-11-24
 * Created on 2015-11-24.
 */

#pragma once

namespace smtrat
{
	struct ICESettings1
	{
		static constexpr auto moduleName = "ICEModule<ICESettings1>";

		static constexpr bool dumpAsDot = false;
		static constexpr auto dotFilename = "licgraph.dot";
	};
}
