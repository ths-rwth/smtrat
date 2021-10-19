#pragma once

#include "../config.h"
#include "ValidationPoint.h"

namespace smtrat {
    using ValidationPoint = smtrat::validation::ValidationPoint;

    template<typename T>
    auto& validation_get(const std::string& name) {
        return smtrat::validation::get<T>(name);
    }

    // TODO validation settings: turn on and off validation points or channels?

    #ifdef SMTRAT_DEVOPTION_Validation
        #define SMTRAT_VALIDATION_INIT(channel, class, member, name) class& member = smtrat::validation::get<class>(channel + "." + name)
        #define SMTRAT_VALIDATION_ADD(channel, member,formula) {auto id = member.add(formula); SMTRAT_LOG_DEBUG(channel, "Assumption " << member.name() << " #" << id << ": " << formula); }
    #else
        #define SMTRAT_VALIDATION_INIT(class, member, name)
        #define SMTRAT_VALIDATION_ADD(channel, member,formula)
    #endif
}