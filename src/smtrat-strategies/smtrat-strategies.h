#pragma once

#include <smtrat-solver/Manager.h>

// Use absolute include, otherwise cmake fails to add dependencies for config.h
#include <smtrat-strategies/config.h>

namespace smtrat {

void load_configured_strategy(Manager& m);

}