#pragma once

#include "../solver/Manager.h"

#include "../modules/CADModule/CADModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	class CADOnlyGuess: public Manager
	{
		public:
			CADOnlyGuess(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<CADModule<CADSettingsGuessAndSplit>>()
					})
				});
			}
	};
}	// namespace smtrat
