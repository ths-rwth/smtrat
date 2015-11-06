/**
 * @file PreprocessingOne.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/EMModule/EMModule.h"
#include "../modules/PFEModule/PFEModule.h"
#include "../modules/SplitSOSModule/SplitSOSModule.h"
#include "../modules/ESModule/ESModule.h"
#include "../modules/LICModule/LICModule.h"
#include "../modules/BEModule/BEModule.h"

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
    class PreprocessingOne:
        public Manager
    {
        public:
            PreprocessingOne(): Manager() {
				setStrategy({
					addBackend<BEModule<BESettings1>>(
						addBackend<LICModule<LICSettings1>>(
							addBackend<EMModule<EMSettings1>>(
								addBackend<PFEModule<PFESettings1>>(
							//		addBackend<SplitSOSModule<SplitSOSSettings1>>({
										addBackend<ESModule<ESSettings1>>()
							//		})
								)
							)
						)
					)
				});
			}

    };

}    // namespace smtrat
