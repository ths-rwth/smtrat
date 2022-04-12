#pragma once

#include <smtrat-solver/Manager.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/NewCoveringModule/NewCoveringModule.h>

namespace smtrat
{
	class NewCovering: public Manager
	{
		public:
			NewCovering(): Manager() {
				setStrategy(
					addBackend<SATModule<SATSettings1>>(
						addBackend<NewCoveringModule<NewCoveringSettings1>>()
					)
				);
			}
	};
}
