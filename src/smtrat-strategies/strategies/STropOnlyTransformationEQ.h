#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/STropModule/STropModule.h>

namespace smtrat
{
	class STropOnlyTransformationEQ: public Manager
	{
		public:
			STropOnlyTransformationEQ(): Manager() {
				setStrategy({
					addBackend<STropModule<STropSettings2>>()
				});
			}
	};
}	// namespace smtrat
