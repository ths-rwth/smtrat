#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/STropModule/STropModule.h>

namespace smtrat
{
	class STropOnly: public Manager
	{
		public:
			STropOnly(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<STropModule<STropSettings1>>()
					})
				});
			}
	};
}	// namespace smtrat
