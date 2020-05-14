#pragma once

#include "../config.h"
#include <carl-statistics/Statistics.h>

namespace smtrat {
    using Statistics = carl::statistics::Statistics;

    template<typename T>
    auto& statistics_get(const std::string& name) {
        return carl::statistics::get<T>(name);
    }

    #ifdef SMTRAT_DEVOPTION_Statistics
        #define SMTRAT_INIT_STATISTICS(class, member, name) class& member = carl::statistics::get<class>(name)
        #define SMTRAT_CALL_STATISTICS(function) function
        #define SMTRAT_TIME_START() carl::statistics::timer::start()
        #define SMTRAT_TIME_FINISH(timer, start) timer.finish(start)
    #else
        #define SMTRAT_INIT_STATISTICS(class, member, name)
        #define SMTRAT_CALL_STATISTICS(function)
        #define SMTRAT_TIME_START() carl::statistics::timing::time_point()
        #define SMTRAT_TIME_FINISH(timer, start) static_cast<carl::statistics::timing::time_point>(start)
    #endif
}
