#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/FMPlexModule/FMPlexModule.h>

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
class FMPlex_BranchLevel: public Manager {
public:
   	FMPlex_BranchLevel(): Manager()
    {
	   	setStrategy(
		{
				addBackend<SATModule<SATSettings1>>(
				{
					addBackend<FMPlexModule<FMPlexSettingsBranchLevel>>()
			})
		});
    }
};
} // namespace smtrat