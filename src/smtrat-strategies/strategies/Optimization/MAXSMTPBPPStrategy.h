#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/LRAModule/LRAModule.h>
#include <smtrat-modules/PBPPModule/PBPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>


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
