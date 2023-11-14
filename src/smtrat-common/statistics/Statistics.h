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
        #define SMTRAT_STATISTICS_INIT(class, variable, name) class& variable = carl::statistics::get<class>(name)
        #define SMTRAT_STATISTICS_INIT_STATIC(class, variable, name) static class& variable = carl::statistics::get<class>(name)
        #define SMTRAT_STATISTICS_CALL(function) function
        #define SMTRAT_TIME_START(variable) auto variable = carl::statistics::Timer::start()
        #define SMTRAT_TIME_FINISH(timer, variable) timer.finish(variable)
    #else
        #define SMTRAT_STATISTICS_INIT(class, variable, name)
        #define SMTRAT_STATISTICS_INIT_STATIC(class, variable, name)
        #define SMTRAT_STATISTICS_CALL(function)
        #define SMTRAT_TIME_START(variable)
        #define SMTRAT_TIME_FINISH(timer, start)
    #endif
}
