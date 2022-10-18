#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/STropModule/STropModule.h>

namespace smtrat
{
	class STropTransformationEQ: public Manager
	{
		public:
			STropTransformationEQ(): Manager() {
				setStrategy({
					addBackend<FPPModule<FPPSettings1>>({
						addBackend<STropModule<STropSettings2>>()
					})
				});
			}
	};
}	// namespace smtrat
