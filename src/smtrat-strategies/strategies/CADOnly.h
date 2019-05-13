#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/NewCADModule/NewCADModule.h>
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class CADOnly: public Manager
	{
		public:
			CADOnly(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<NewCADModule<NewCADSettingsFOS>>()
					})
				});
			}
	};
}	// namespace smtrat
