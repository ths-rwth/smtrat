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
				setStrategy(std::initializer_list<BackendLink>{
					addBackend<LICModule<LICSettings1>>(std::initializer_list<BackendLink>{
						addBackend<EMModule<EMSettings1>>(std::initializer_list<BackendLink>{
							addBackend<PFEModule<PFESettings1>>(std::initializer_list<BackendLink>{
								addBackend<SplitSOSModule<SplitSOSSettings1>>(std::initializer_list<BackendLink>{
									addBackend<ESModule<ESSettings1>>(
										addBackend<BEModule<BESettings1>>(
											addBackend<CBModule<CBSettings1>>()
										)
									)
								})
							})
						})
					})
				});
			}

    };

}    // namespace smtrat
