#pragma once

#include "../solver/Manager.h"

#include "../modules/NLSATModule/NLSATModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class NLSAT: public Manager
	{
		public:
			NLSAT(): Manager() {
				setStrategy(
					addBackend<SATModule<SATSettingsMCSAT>>()
				);
			}
	};
}	// namespace smtrat
