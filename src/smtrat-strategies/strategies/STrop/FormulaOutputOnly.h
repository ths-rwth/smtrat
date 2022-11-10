#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/STropModule/STropModule.h>

namespace smtrat
{
	class STrop_FormulaOutputOnly: public Manager
	{
		public:
			STrop_FormulaOutputOnly(): Manager() {
				setStrategy({
					// addBackend<FPPModule<FPPSettings1>>({
						addBackend<STropModule<STropSettings3OutputOnly>>()
					// })
				});
			}
	};
}	// namespace smtrat
