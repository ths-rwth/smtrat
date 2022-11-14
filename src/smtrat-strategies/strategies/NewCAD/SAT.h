#pragma once

#include "../solver/Manager.h"

#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class NewCAD_SAT: public Manager
	{
		public:
			NewCAD_SAT(): Manager() {
				setStrategy(
					addBackend<SATModule<SATSettings1>>(
					)
				);
			}
	};
}	// namespace smtrat
