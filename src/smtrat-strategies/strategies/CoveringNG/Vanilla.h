#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {
class CoveringNG_Vanilla : public Manager {
public:
    CoveringNG_Vanilla() : Manager() {
        setStrategy(addBackend<CoveringNGModule<CoveringNGSettingsDefault>>());
    }
};
} // namespace smtrat
