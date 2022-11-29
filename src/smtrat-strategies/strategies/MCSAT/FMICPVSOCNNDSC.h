#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class MCSAT_FMICPVSOCNNDSC: public Manager
	{
		public:
			MCSAT_FMICPVSOCNNDSC(): Manager() {
				setStrategy(
					addBackend<FPPModule<FPPSettings1>>(
						addBackend<SATModule<SATSettingsMCSATFMICPVSOCNNDSC>>()
					)
				);
			}
	};
}	// namespace smtrat
