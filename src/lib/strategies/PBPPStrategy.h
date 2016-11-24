#pragma once

#include "../solver/Manager.h"

#include "../modules/BEModule/PBPPModule.h"


namespace smtrat
{
    class AllModulesStrategy:
        public Manager
    {
        public:
            AllModulesStrategy(): Manager() {
				setStrategy({
					addBackend<PBPPModule<PBPPSettings1>>(),

				});
			}
    };
}    // namespace smtrat
