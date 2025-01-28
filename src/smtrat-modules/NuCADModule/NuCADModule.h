#pragma once

#include <smtrat-solver/Module.h>
#include "NuCADSettings.h"

namespace smtrat {

template<typename Settings>
class NuCADModule : public Module {
private:


public:
    using SettingsType = Settings;

    NuCADModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = nullptr);

    ~NuCADModule();

    bool informCore(const FormulaT& _constraint);
    bool addCore(ModuleInput::const_iterator _subformula);
    void removeCore(ModuleInput::const_iterator _subformula);
    void updateModel() const;
    Answer checkCore();
};
} // namespace smtrat
