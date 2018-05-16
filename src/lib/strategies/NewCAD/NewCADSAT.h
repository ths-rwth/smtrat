#pragma once

#include "../solver/Manager.h"

#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class NewCADSAT: public Manager
	{
		public:
			NewCADSAT(): Manager() {
				setStrategy(
					addBackend<SATModule<SATSettings1>>(
					)
				);
			}
	};
}	// namespace smtrat
