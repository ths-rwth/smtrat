/**
* @file FMPlexSolver.h
*/
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
class FMPlexSolver: public Manager {
public:
   FMPlexSolver(): Manager()
   {
	   setStrategy(
		   {
			   addBackend<SATModule<SATSettings1>>(
				   {
					   addBackend<NewFMPlexModule<NewFMPlexSettings>>()
				   })

		   });
   }
};
} // namespace smtrat
