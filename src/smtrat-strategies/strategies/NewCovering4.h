#pragma once

#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/NewCoveringModule/NewCoveringModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
class NewCovering4 : public Manager {
public:
    NewCovering4()
        : Manager() {
        setStrategy(
            addBackend<SATModule<SATSettings1>>(
                addBackend<NewCoveringModule<NewCoveringSettings4>>()));
    }
};
} // namespace smtrat
