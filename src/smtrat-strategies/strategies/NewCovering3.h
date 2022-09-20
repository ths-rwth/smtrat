#pragma once

#include <smtrat-modules/NewCoveringModule/NewCoveringModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
class NewCovering3 : public Manager {
public:
    NewCovering3()
        : Manager() {
        setStrategy(
            addBackend<SATModule<SATSettings1>>(
                addBackend<NewCoveringModule<NewCoveringSettings3>>()));
    }
};
} // namespace smtrat
