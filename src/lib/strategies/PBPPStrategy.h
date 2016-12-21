#pragma once

#include "../solver/Manager.h"

#include "../modules/PBPPModule/PBPPModule.h"


namespace smtrat
{
    class PBPPStrategy:
        public Manager
    {
        public:
            PBPPStrategy(): Manager() {
				setStrategy({
					addBackend<PBPPModule<PBPPSettings1>>(),

				});
			}
    };
}    // namespace smtrat
