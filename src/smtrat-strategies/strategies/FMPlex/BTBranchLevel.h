#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/NewFMPlexModule/NewFMPlexModule.h>

namespace smtrat
{
/**
	* Strategy description.
	*
	* @author
	* @since
	* @version
	*
*/
class FMPlex_BTBranchLevel: public Manager {
public:
   	FMPlex_BTBranchLevel(): Manager()
    {
	   	setStrategy(
		{
				addBackend<SATModule<SATSettings1>>(
				{
					addBackend<NewFMPlexModule<NewFMPlexSettingsBTBranchLevel>>()
			})
		});
    }
};
} // namespace smtrat