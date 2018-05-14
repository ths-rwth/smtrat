#pragma once

#include "../solver/Manager.h"

#include "../modules/LRAModule/LRAModule.h"
#include "../modules/PBPPModule/PBPPModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/ICPModule/ICPModule.h"


namespace smtrat
{
    class PBPPStrategy2:
        public Manager
    {
        public:
            PBPPStrategy2(): Manager() {
				setStrategy({
					addBackend<PBPPModule<PBPPSettings1>>(
						addBackend<SATModule<SATSettings1>>(
							addBackend<ICPModule<ICPSettings1>>(
								addBackend<LRAModule<LRASettings1>>()
							)
						)
					),
				});
			}
    };
}    // namespace smtrat
