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
        #define SMTRAT_STATISTICS_INIT(class, member, name) class& member = carl::statistics::get<class>(name)
        #define SMTRAT_STATISTICS_INIT_STATIC(class, member, name) static class& member = carl::statistics::get<class>(name)
        #define SMTRAT_STATISTICS_CALL(function) function
        #define SMTRAT_TIME_START() carl::statistics::timer::start()
        #define SMTRAT_TIME_FINISH(timer, start) timer.finish(start)
    #else
        #define SMTRAT_STATISTICS_INIT(class, member, name)
        #define SMTRAT_STATISTICS_INIT_STATIC(class, member, name)
        #define SMTRAT_STATISTICS_CALL(function)
        #define SMTRAT_TIME_START() carl::statistics::timing::time_point()
        #define SMTRAT_TIME_FINISH(timer, start)
    #endif
}
