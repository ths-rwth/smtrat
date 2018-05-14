#pragma once

#include "../solver/Manager.h"

#include "../modules/LRAModule/LRAModule.h"
#include "../modules/PBPPModule/PBPPModule.h"
#include "../modules/SATModule/SATModule.h"


namespace smtrat
{
    class PBPPStrategy:
        public Manager
    {
        public:
            PBPPStrategy(): Manager() {
				setStrategy({
					addBackend<PBPPModule<PBPPSettings1>>(
						addBackend<SATModule<SATSettings1>>(
							addBackend<LRAModule<LRASettings1>>()
						)
					),
				});
			}
    };
}    // namespace smtrat
