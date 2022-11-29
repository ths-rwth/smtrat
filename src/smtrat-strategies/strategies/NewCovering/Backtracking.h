#pragma once

#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/NewCoveringModule/NewCoveringModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
class NewCovering_Backtracking : public Manager {
public:
    NewCovering_Backtracking()
        : Manager() {
        setStrategy(
            addBackend<SATModule<SATSettings1>>(
                addBackend<NewCoveringModule<NewCoveringSettings3>>()));
    }
};
} // namespace smtrat
