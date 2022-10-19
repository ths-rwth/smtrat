#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/STropModule/STropModule.h>

namespace smtrat
{
	class STropFormula: public Manager
	{
		public:
			STropFormula(): Manager() {
				setStrategy({
					addBackend<FPPModule<FPPSettings1>>({
						addBackend<STropModule<STropSettings3>>()
					})
				});
			}
	};
}	// namespace smtrat
