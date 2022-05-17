#pragma once

#include <smtrat-modules/NewCoveringModule/NewCoveringModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
class NewCovering2 : public Manager {
public:
    NewCovering2()
        : Manager() {
        setStrategy(
            addBackend<SATModule<SATSettings1>>(
                addBackend<NewCoveringModule<NewCoveringSettings2>>()));
    }
};
} // namespace smtrat
