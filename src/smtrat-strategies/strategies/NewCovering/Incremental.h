#pragma once

#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/NewCoveringModule/NewCoveringModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
class NewCovering_Incremental : public Manager {
public:
    NewCovering_Incremental()
        : Manager() {
        setStrategy(
            addBackend<SATModule<SATSettings1>>(
                addBackend<NewCoveringModule<NewCoveringSettings2>>()));
    }
};
} // namespace smtrat
