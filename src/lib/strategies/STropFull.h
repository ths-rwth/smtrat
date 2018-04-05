#pragma once

#include "../solver/Manager.h"

#include "../modules/SATModule/SATModule.h"
#include "../modules/STropModule/STropModule.h"
#include "../modules/ICPModule/ICPModule.h"
#include "../modules/VSModule/VSModule.h"
#include "../modules/CADModule/CADModule.h"

namespace smtrat
{
	class STropFull: public Manager
	{
		public:
            STropFull(): Manager() {
                setStrategy({
                    addBackend<SATModule<SATSettings1>>({
                        addBackend<STropModule<STropSettings1>>({
                            addBackend<ICPModule<ICPSettings1>>({
                                addBackend<VSModule<VSSettings234>>({
                                    addBackend<CADModule<CADSettingsSplitPath>>()
                                })
                            })
                        })
                    })
                });
            }
	};
}	// namespace smtrat
