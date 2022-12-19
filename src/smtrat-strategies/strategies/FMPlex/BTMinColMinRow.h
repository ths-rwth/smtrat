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
class FMPlex_BTMinColMinRow: public Manager {
public:
   FMPlex_BTMinColMinRow(): Manager()
   {
	   setStrategy(
		   {
			   addBackend<SATModule<SATSettings1>>(
				   {
					   addBackend<NewFMPlexModule<NewFMPlexSettingsBTMinColMinRow>>()
				   })

		   });
   }
};
} // namespace smtrat