#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/NewCADModule/NewCADModule.h>
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MISHybrid: public Manager
	{
		public:
			MISHybrid(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<NewCADModule<NewCADSettingsMISHybrid>>()
					})
				});
			}
	};
}	// namespace smtrat
