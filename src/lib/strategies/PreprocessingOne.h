/**
 * @file PreprocessingOne.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/EMModule/EMModule.h"
#include "../modules/RPFModule/RPFModule.h"
#include "../modules/SplitSOSModule/SplitSOSModule.h"
#include "../modules/ESModule/ESModule.h"
#include "../modules/BEModule/BEModule.h"
#include "../modules/CBModule/CBModule.h"

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
					addBackend<EMModule<EMSettings1>>({
						addBackend<RPFModule<RPFSettings1>>({
							addBackend<SplitSOSModule<SplitSOSSettings1>>({
								addBackend<ESModule<ESSettings1>>({
									addBackend<BEModule<BESettings1>>(
										addBackend<CBModule<CBSettings1>>()
									)
								})
							})
						})
					})
				});
			}

    };

}    // namespace smtrat
