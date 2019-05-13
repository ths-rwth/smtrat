#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/NewCADModule/NewCADModule.h>
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MISGreedyPre: public Manager
	{
		public:
			MISGreedyPre(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<NewCADModule<NewCADSettingsMISGreedyPre>>()
					})
				});
			}
	};
}	// namespace smtrat
