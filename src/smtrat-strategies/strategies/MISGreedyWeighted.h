#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/NewCADModule/NewCADModule.h>
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MISGreedyWeighted: public Manager
	{
		public:
			MISGreedyWeighted(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<NewCADModule<NewCADSettingsMISGreedyWeighted>>()
					})
				});
			}
	};
}	// namespace smtrat
