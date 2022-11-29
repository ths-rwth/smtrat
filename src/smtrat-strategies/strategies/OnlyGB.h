#pragma once

#include "../solver/Manager.h"

#include "../modules/GBModule/GBModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class OnlyGB: public Manager
	{
		public:
			OnlyGB(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<GBModule<GBSettings1>>()
					})
				});
			}
	};
}	// namespace smtrat
