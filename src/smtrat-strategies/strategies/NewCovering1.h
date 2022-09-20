#pragma once

#include <smtrat-modules/NewCoveringModule/NewCoveringModule.h>
#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
class NewCovering1 : public Manager {
public:
    NewCovering1()
        : Manager() {
        setStrategy(
            addBackend<SATModule<SATSettings1>>(
                addBackend<NewCoveringModule<NewCoveringSettings1>>()));
    }
};
} // namespace smtrat
