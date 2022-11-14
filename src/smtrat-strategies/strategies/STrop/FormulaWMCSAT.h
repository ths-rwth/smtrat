#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/STropModule/STropModule.h>
#include <smtrat-modules/SATModule/SATModule.h>

namespace smtrat
{
	class STrop_FormulaWMCSAT: public Manager
	{
		public:
			STrop_FormulaWMCSAT(): Manager() {
				setStrategy({
					addBackend<FPPModule<FPPSettings1>>({
						addBackend<STropModule<STropSettings3>>({
							addBackend<SATModule<SATSettingsMCSATFMICPVSOCNewOC>>()
						})
					})
				});
			}
	};
}	// namespace smtrat
