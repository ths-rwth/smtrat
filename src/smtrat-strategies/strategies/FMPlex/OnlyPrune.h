#pragma once

#include <smtrat-solver/Manager.h>

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
class FMPlex_OnlyPrune: public Manager {
public:
   FMPlex_OnlyPrune(): Manager()
   {
	   setStrategy(
		   {
			   addBackend<SATModule<SATSettings1>>(
				   {
					   addBackend<NewFMPlexModule<NewFMPlexSettingsOnlyPrune>>()
				   })

		   });
   }
};
} // namespace smtrat
