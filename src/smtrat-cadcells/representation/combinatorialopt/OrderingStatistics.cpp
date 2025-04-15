#include "OrderingStatistics.h"

#ifdef SMTRAT_DEVOPTION_Statistics
namespace smtrat {
namespace cadcells::representation::combinatorialopt {
    OrderingStatistics &ordering_statistics() {
        static OrderingStatistics &stats = statistics_get<OrderingStatistics>("combinatorialopt");
        return stats;
    }
}
}
#endif
