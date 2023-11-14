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

Note that neither the key nor the value are allowed to contain spaces, `(` or `)`.

This is then instantiated by calling

    #ifdef SMTRAT_DEVOPTION_Statistics
    auto& myStatistics = statistics_get<myModule::MyStatistics>("MyModuleName");
    #endif

or, as shortcut

    SMTRAT_STATISTICS_INIT(myModule::MyStatistics, myStatistics, "MyModuleName")


and statistics can be collected by calling the user defined operations (e.g. `myStatistics.count()`).

All statistics-related code should be encapsulated by the `SMTRAT_DEVOPTION_Statistics` flag. Alternatively, code can be encapsulated in `SMTRAT_STATISTICS_CALL()`.

### Series, Dynamic Counters, Serialization

You can pass the following data types to `addKeyValuePair`:
* `Series`: You can add values to the series. During collection, the average, the min, the max and the number of values is computed. The values are not stored.
* `MultiCounter`: You can increase a counter by some value w.r.t. some key. Different keys refer to different counters. During collection, a list of all counter values by key is stored.

Further, some default data types can safely passed as value to `addKeyValuePair`. As of writing, this is `std::pair`, however, this will be extended in future.

### Timing

The statistics framework has the ability to easily collect timings.

The following code will measure the total running time of the code block as well as the number of times the code block was executed:

    class MyStatistics : public Statistics {
    private:
        carl::statistics::Timer mTimer;

    public:
        void collect() {
            Statistics::addKeyValuePair("timer", mTimer);
        }
        auto& timer() {
            return mTimer;
        }
    };

    SMTRAT_STATISTICS_INIT(myModule::MyStatistics, myStatistics, "MyModuleName")

    SMTRAT_TIME_START(start);
	// expensive code
	SMTRAT_TIME_FINISH(myStatistics.timer(), start);


The measured timings will then appear alongside the statistics.

Note that the resolution of these measurements is in 1 millisecond. Thus, be careful when interpreting results; especially, it measured code blocks should be big enough.