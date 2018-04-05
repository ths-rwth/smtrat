#pragma once

#include "../solver/Manager.h"

#include "../modules/SATModule/SATModule.h"
#include "../modules/CSplitModule/CSplitModule.h"

namespace smtrat
{
	class CSplitOnly: public Manager
	{
		public:
			CSplitOnly(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
                        addBackend<CSplitModule<CSplitSettings1>>()
                    })
                });
			}
	};
}	// namespace smtrat
