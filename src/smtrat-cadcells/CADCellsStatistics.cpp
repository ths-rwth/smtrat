#include "CADCellsStatistics.h"

#ifdef SMTRAT_DEVOPTION_Statistics
namespace smtrat {
namespace cadcells {
    CADCellsStatistics &statistics() {
        static CADCellsStatistics &stats = statistics_get<CADCellsStatistics>("smtrat-cadcells");
        return stats;
    }
}
}
#endif
