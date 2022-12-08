#pragma once

#include <smtrat-solver/Manager.h>

// #include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/STropModule/STropModule.h>

namespace smtrat
{
	class STrop_TransformationEQOutputOnly: public Manager
	{
		public:
			STrop_TransformationEQOutputOnly(): Manager() {
				setStrategy({
					// addBackend<FPPModule<FPPSettings1>>({
						addBackend<STropModule<STropSettings2OutputOnly>>()
					// })
				});
			}
	};
}	// namespace smtrat
