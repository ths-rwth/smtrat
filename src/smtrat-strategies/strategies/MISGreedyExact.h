#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/NewCADModule/NewCADModule.h>
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MISTrivial: public Manager
	{
		public:
			MISTrivial(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<NewCADModule<NewCADSettingsMISTrivial>>()
					})
				});
			}
	};
}	// namespace smtrat
