/**
 * @file NRASolver.h
 */
#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/VSModule/VSModule.h>
#include <smtrat-modules/NewCADModule/NewCADModule.h>

namespace smtrat
{
	/**
	 * Strategy description.
	 *
	 * @author
	 * @since
	 * @version
	 *
	 */
	class NRA_VSCAD: public Manager {
	public:
		NRA_VSCAD(): Manager() {
			setStrategy({
				addBackend<FPPModule<FPPSettings1>>(
					addBackend<SATModule<SATSettings1>>(
						addBackend<VSModule<VSSettings234>>(
							addBackend<NewCADModule<NewCADSettingsFOS>>()
						)
					)
				)
			});
		}
	};
} // namespace smtrat
