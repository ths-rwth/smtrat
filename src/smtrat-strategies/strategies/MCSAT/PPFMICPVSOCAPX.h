#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/STropModule/STropModule.h>

namespace smtrat
{
	class MCSAT_PPFMICPVSOCAPX: public Manager
	{
		public:
			MCSAT_PPFMICPVSOCAPX(): Manager() {
				setStrategy(
					addBackend<FPPModule<FPPSettings1>>({
						addBackend<STropModule<STropSettings3>>({
							addBackend<SATModule<SATSettingsMCSATAPX>>()
						})
					})
				);
			}
	};
}	// namespace smtrat
