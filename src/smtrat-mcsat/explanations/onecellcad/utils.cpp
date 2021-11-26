#include "utils.h"

#ifdef SMTRAT_DEVOPTION_Statistics
namespace smtrat {
namespace mcsat {
namespace onecellcad {
    OCStatistics &getStatistic() {
        static OCStatistics &mStatistics = statistics_get<OCStatistics>("mcsat-explanation-onecellcad");
        return mStatistics;
    }
}
}
}
#endif
