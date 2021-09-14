#include "utils.h"

#ifdef SMTRAT_DEVOPTION_Statistics
    OCStatistics& getStatistic(){
        static OCStatistics& mStatistics = statistics_get<OCStatistics>("mcsat-explanation-onecellcad");
    }
#endif
