/**
 * @file RatComp2016.h
 */
#pragma once

#include "../solver/Manager.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/IncWidthModule/IncWidthModule.h"
#include "../modules/IntBlastModule/IntBlastModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/LRAModule/LRAModule.h"
#include "../modules/VSModule/VSModule.h"
#include "../modules/NewCADModule/NewCADModule.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/ICPModule/ICPModule.h"
#include "../modules/VSModule/VSModule.h"
#include "../modules/CADModule/CADModule.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/CubeLIAModule/CubeLIAModule.h"
#include "../modules/LRAModule/LRAModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/LRAModule/LRAModule.h"
#include "../modules/FPPModule/FPPModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/STropModule/STropModule.h"
#include "../modules/LRAModule/LRAModule.h"

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
    class ActaNRA:
        public Manager
    {
        public:

        ActaNRA(): Manager()
        {
            setStrategy(
            {
                addBackend<FPPModule<FPPSettings1>>(
                    addBackend<SATModule<SATSettings1>>(
                        addBackend<STropModule<STropSettings1>>(
                            addBackend<ICPModule<ICPSettings1>>(
                                addBackend<VSModule<VSSettings234>>(
                                    addBackend<NewCADModule<NewCADSettingsFU>>()
                                )
                            )
                        )
                    )
                )
            });
        }
    };
} // namespace smtrat
