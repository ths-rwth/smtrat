#pragma once

#include "../solver/Manager.h"

#include "../modules/SATModule/SATModule.h"
#include "../modules/ICPModule/ICPModule.h"
#include "../modules/VSModule/VSModule.h"
#include "../modules/CADModule/CADModule.h"

namespace smtrat
{
	class Backends: public Manager
	{
		public:
            Backends(): Manager() {
                setStrategy({
                    addBackend<SATModule<SATSettings1>>({
                        addBackend<ICPModule<ICPSettings1>>({
                            addBackend<VSModule<VSSettings234>>({
                                addBackend<CADModule<CADSettingsSplitPath>>()
                            })
                        })
                    })
                });
            }
	};
}	// namespace smtrat
