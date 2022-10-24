#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/STropModule/STropModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/NewCoveringModule/NewCoveringModule.h>
#include <smtrat-modules/NewCADModule/NewCADModule.h>

namespace smtrat
{
	class STropFormulaWCADBackends: public Manager
	{
		public:
			STropFormulaWCADBackends(): Manager() {
				setStrategy({
					addBackend<FPPModule<FPPSettings1>>({
						addBackend<STropModule<STropSettings3>>({
							addBackend<SATModule<SATSettings1>>({
								addBackend<NewCoveringModule<NewCoveringSettings2>>({
									addBackend<NewCADModule<NewCADSettingsFOS>>()
								})
							})
						})
					})
				});
			}
	};
}	// namespace smtrat
