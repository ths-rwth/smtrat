## Statistics and timing {#statistics-and-timing}

### Statistics

SMT-RAT has the ability to collect statistics after the solving process is finished.

For enabling this feature, the `SMTRAT_DEVOPTION_Statistics` needs to be turned on in the CMake settings.

#### Collecting statistics

A statistics object can be created by inheriting from `Statistics.h`:

```
#pragma once

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat {
namespace myModule {

class MyStatistics : public Statistics {
private:
    std::size_t mCounter = 0;

public:
    void collect() { // called after the solving process to collect statistics
        Statistics::addKeyValuePair("counter", mCounter);
    }
    void count() { // user defined
        ++mCounter;
    }
};

}
}
#endif
```

This is then instantiated by calling

    #ifdef SMTRAT_DEVOPTION_Statistics
    auto& myStatistics = statistics_get<myModule::MyStatistics>("MyModuleName");
    #endif

and statistics can be collected by calling the user defined operations (e.g. `myStatistics.count()`).

All statistics-related code should be encapsulated by the `SMTRAT_DEVOPTION_Statistics` flag.

### Timing

CARL has the ability to easily collect timings. To enable this feature, CARL must be compiled with `TIMING` set to `ON` in CMake. SMT-RAT needs to use this this version of CARL. Furthermore, in SMT-RAT `SMTRAT_DEVOPTION_Statistics` needs to be enabled as well.

The following call will measure the total running time of the code block as well as the times the code block was executed:

    #include "../util/TimingCollector.h"

    // ...

    auto start = CARL_TIME_START();
	// expensive code
	CARL_TIME_FINISH("name.of.statistic", start);


The measured timings will then appear alongside the statistics.

Note that the resolution of these measurements is in 1 millisecond. Thus, be careful when interpreting results; especially, it measured code blocks should be big enough.