/**
 * @file PreprocessingOne.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/GBPPModule/GBPPModule.h"
#include "../modules/OPBConverterModule/OPBConverterModule.h"

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
					addBackend<OPBConverterModule<OPBConverterSettings1>>(
						addBackend<GBPPModule<GBPPSettings1>>(
						)
					)
				});
			}

	};

}    // namespace smtrat
