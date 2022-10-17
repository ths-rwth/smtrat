#pragma once

#include <smtrat-solver/Manager.h>

#include <smtrat-modules/STropModule/STropModule.h>

namespace smtrat
{
	class STropOnlyFormula: public Manager
	{
		public:
			STropOnlyFormula(): Manager() {
				setStrategy({
					addBackend<STropModule<STropSettings2>>()
				});
			}
	};
}	// namespace smtrat
