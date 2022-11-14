#pragma once

#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-modules/NewCoveringModule/NewCoveringModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
class NewCovering_IncrementalBacktracking : public Manager {
public:
    NewCovering_IncrementalBacktracking()
        : Manager() {
        setStrategy(
            addBackend<SATModule<SATSettings1>>(
                addBackend<NewCoveringModule<NewCoveringSettings1>>()));
    }
};
} // namespace smtrat
