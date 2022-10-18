#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/STropModule/STropModule.h>

namespace smtrat
{
	class STropIncremental: public Manager
	{
		public:
			STropIncremental(): Manager() {
				setStrategy({
					addBackend<FPPModule<FPPSettings1>>({
						addBackend<SATModule<SATSettings1>>({
							addBackend<STropModule<STropSettings1>>()
						})
					})
				});
			}
	};
}	// namespace smtrat
