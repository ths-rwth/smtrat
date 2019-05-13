#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/NewCADModule/NewCADModule.h>
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MISGreedy: public Manager
	{
		public:
			MISGreedy(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<NewCADModule<NewCADSettingsMISGreedy>>()
					})
				});
			}
	};
}	// namespace smtrat
