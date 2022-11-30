#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/STropModule/STropModule.h>

namespace smtrat
{
	class STrop_FormulaAlt: public Manager
	{
		public:
			STrop_FormulaAlt(): Manager() {
				setStrategy({
					addBackend<FPPModule<FPPSettings1>>({
						addBackend<STropModule<STropSettings3b>>()
					})
				});
			}
	};
}	// namespace smtrat
