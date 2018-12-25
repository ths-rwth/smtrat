#pragma once

#include "../solver/Manager.h"

#include "../modules/SATModule/SATModule.h"
#include "../modules/STropModule/STropModule.h"

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
