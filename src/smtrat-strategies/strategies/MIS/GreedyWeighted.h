#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/NewCADModule/NewCADModule.h>
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MIS_GreedyWeighted: public Manager
	{
		public:
			MIS_GreedyWeighted(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<NewCADModule<NewCADSettingsMISGreedyWeighted>>()
					})
				});
			}
	};
}	// namespace smtrat
