#include "OCApproximationStatistics.h"

#ifdef SMTRAT_DEVOPTION_Statistics
namespace smtrat {
namespace cadcells {
    OCApproximationStatistics &apx_statistics() {
        static OCApproximationStatistics &stats = statistics_get<OCApproximationStatistics>("approximation");
        return stats;
    }
}
}
#endif
