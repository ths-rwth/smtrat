#include "CoveringNGStatistics.h"

#ifdef SMTRAT_DEVOPTION_Statistics
namespace smtrat::covering_ng{
    CoveringNGStatistics &statistics() {
        static CoveringNGStatistics &stats = statistics_get<CoveringNGStatistics>("smtrat-coveringng");
        return stats;
    }
}
#endif
