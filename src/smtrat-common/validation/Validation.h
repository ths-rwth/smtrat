#pragma once

#include "../config.h"
#include "ValidationCollector.h"
#include "ValidationSettings.h"

namespace smtrat {
    inline auto& validation_get(const std::string& channel, const std::string& file, int line) {
        return smtrat::validation::get(channel, file, line);
    }

    #ifdef SMTRAT_DEVOPTION_Validation
        #define SMTRAT_VALIDATION_INIT(channel, variable) auto& variable = smtrat::validation::get(channel, __FILE__, __LINE__)
        #define SMTRAT_VALIDATION_INIT_STATIC(channel, variable) static auto& variable = smtrat::validation::get(channel, __FILE__, __LINE__)
        #define SMTRAT_VALIDATION_ADD_TO(variable, name, formula, consistent) { \
            if (settings_validation().channel_active(variable.channel())) { \
                auto id = variable.add(formula, consistent, name); \
                SMTRAT_LOG_DEBUG(variable.channel(), "Assumption " << variable.identifier() << " #" << id << " (" << name << "): " << formula); \
            } \
        }
        #define SMTRAT_VALIDATION_ADD(channel, name, formula, consistent) { SMTRAT_VALIDATION_INIT_STATIC(channel,tmp); SMTRAT_VALIDATION_ADD_TO(tmp,name,formula,consistent); }
    #else
        #define SMTRAT_VALIDATION_INIT(channel, variable)
        #define SMTRAT_VALIDATION_INIT_STATIC(channel, name)
        #define SMTRAT_VALIDATION_ADD_TO(variable, name, formula, consistent)
        #define SMTRAT_VALIDATION_ADD(channel, name, formula, consistent)
    #endif
}