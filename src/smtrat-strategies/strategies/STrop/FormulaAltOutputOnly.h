#pragma once

#include <smtrat-solver/Manager.h>

// #include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/STropModule/STropModule.h>

namespace smtrat
{
	class STrop_FormulaAltOutputOnly: public Manager
	{
		public:
			STrop_FormulaAltOutputOnly(): Manager() {
				setStrategy({
					// addBackend<FPPModule<FPPSettings1>>({
						addBackend<STropModule<STropSettings3bOutputOnly>>()
					// })
				});
			}
	};
}	// namespace smtrat
