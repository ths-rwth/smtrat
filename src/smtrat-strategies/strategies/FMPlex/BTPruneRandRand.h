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
class FMPlex_BTPruneRandRand: public Manager {
public:
   FMPlex_BTPruneRandRand(): Manager()
   {
	   setStrategy(
		   {
			   addBackend<SATModule<SATSettings1>>(
				   {
					   addBackend<NewFMPlexModule<NewFMPlexSettingsBTPruneRandRand>>()
				   })

		   });
   }
};
} // namespace smtrat