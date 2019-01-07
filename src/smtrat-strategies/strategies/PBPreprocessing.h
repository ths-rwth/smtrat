/**
 * @file PreprocessingOne.h
 */
#pragma once

#include <smtrat-solver/Manager.h>
#include <smtrat-modules/GBPPModule/GBPPModule.h>
#include <smtrat-modules/ESModule/ESModule.h>
// #include "../modules/PBPPModule/PBPPModule.h"

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
	class PBPreprocessing:
		public Manager
	{
		public:
			PBPreprocessing(): Manager() {
				setStrategy({
						//addBackend<GBPPModule<GBPPSettings1>>(
							//addBackend<PBPPModule<PBPPSettings1>>(
								addBackend<ESModule<ESSettings1>>()
							//)
						//)
				});
			}

	};

	class PBPreprocessingGroebner:
		public Manager
	{
		public:
			PBPreprocessingGroebner(): Manager() {
				setStrategy({
						addBackend<GBPPModule<GBPPSettings1>>(
							//addBackend<PBPPModule<PBPPSettings1>>(
								addBackend<ESModule<ESSettings1>>()
							//)
						)
				});
			}

	};

}    // namespace smtrat
