#pragma once

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics
 
namespace smtrat {
namespace cli {
 
class CLIStatistics : public Statistics {
public:
    carl::statistics::Timer parsing;
    void collect() {
        Statistics::addKeyValuePair("parsing", parsing);
    }
};

static auto& statistics() {
    SMTRAT_STATISTICS_INIT_STATIC(CLIStatistics, stats, "cli");
    return stats;
}
 
}
}
#endif
