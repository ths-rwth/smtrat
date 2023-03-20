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
class FMPlex_MinColMinRowPP: public Manager {
public:
   	FMPlex_MinColMinRowPP(): Manager()
    {
	   	setStrategy(
		{
			addBackend<FPPModule<FPPSettings1>>(
            {
				addBackend<SATModule<SATSettings1>>(
				{
					addBackend<FMPlexModule<FMPlexSettingsMinColMinRow>>()
				})
			})
		});
    }
};
} // namespace smtrat