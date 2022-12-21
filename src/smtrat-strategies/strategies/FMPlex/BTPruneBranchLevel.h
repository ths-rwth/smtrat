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
class FMPlex_BTPruneBranchLevel: public Manager {
public:
   	FMPlex_BTPruneBranchLevel(): Manager()
    {
	   	setStrategy(
		{
			addBackend<FPPModule<FPPSettings1>>(
            {
				addBackend<SATModule<SATSettings1>>(
				{
					addBackend<NewFMPlexModule<NewFMPlexSettingsBTPruneBranchLevel>>()
				})
			})
		});
    }
};
} // namespace smtrat