#pragma once

#include "../config.h"
#include "ValidationCollector.h"
#include "ValidationSettings.h"

namespace smtrat {
    inline auto& validation_get(const std::string& channel, const std::string& name) {
        return smtrat::validation::get(channel, name);
    }

    #ifdef SMTRAT_DEVOPTION_Validation
        #define SMTRAT_VALIDATION_INIT(channel, name, member) auto& member = smtrat::validation::get(channel, name)
        #define SMTRAT_VALIDATION_ADD_TO(member, formula, consistent) { \
            if (settings_validation().channel_active(member.channel())) { \
                auto id = member.add(formula, consistent); \
                SMTRAT_LOG_DEBUG(member.channel(), "Assumption " << member.name() << " #" << id << ": " << formula); \
            } \
        }
        #define SMTRAT_VALIDATION_ADD(channel, name, formula, consistent) { static SMTRAT_VALIDATION_INIT(channel,name,tmp); SMTRAT_VALIDATION_ADD_TO(tmp,formula,consistent); }
    #else
        #define SMTRAT_VALIDATION_INIT(channel, name, member)
        #define SMTRAT_VALIDATION_ADD(member, formula, consistent)
        #define SMTRAT_VALIDATION_ADD(channel, name, formula, consistent)
    #endif
}