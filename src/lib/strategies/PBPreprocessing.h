/**
 * @file PreprocessingOne.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/EMModule/EMModule.h"
#include "../modules/PFEModule/PFEModule.h"
#include "../modules/SplitSOSModule/SplitSOSModule.h"
#include "../modules/ESModule/ESModule.h"
#include "../modules/ICEModule/ICEModule.h"
#include "../modules/MCBModule/MCBModule.h"
#include "../modules/GBPPModule/GBPPModule.h"
#include "../modules/SymmetryModule/SymmetryModule.h"

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
						addBackend<GBPPModule<GBPPSettings1>>()
						});
			}

	};

}    // namespace smtrat
