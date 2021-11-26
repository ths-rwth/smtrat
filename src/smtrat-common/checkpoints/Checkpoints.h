#pragma once

#include "../config.h"
#include <carl-checkpoints/Checkpoints.h>

namespace smtrat {
    #ifdef SMTRAT_DEVOPTION_Checkpoints
    #define SMTRAT_ADD_CHECKPOINT(channel,description,forced,...) carl::checkpoints::CheckpointVerifier::getInstance().push(channel, description, forced, __VA_ARGS__);
    #define SMTRAT_CHECKPOINT(channel,description,...) carl::checkpoints::CheckpointVerifier::getInstance().expect(channel, description, __VA_ARGS__);
    #define SMTRAT_CLEAR_CHECKPOINT(channel) carl::checkpoints::CheckpointVerifier::getInstance().clear(channel);
    #else
    #define SMTRAT_ADD_CHECKPOINT(channel,description,forced,...)
    #define SMTRAT_CHECKPOINT(channel,description,...)
    #define SMTRAT_CLEAR_CHECKPOINT(channel)
    #endif
}
