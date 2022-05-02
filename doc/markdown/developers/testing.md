## Testing {#testing}

SMT-RAT and CArL use [GoogleTest](http://google.github.io/googletest/) for unit testing. To do so, go to the `src/tests/` folder and create a test analogously to the other tests (i.e. creating a new folder, adapting the `CMakeList.txt` in the new folder and in the `tests` folder). *Note that in the SMT-RAT repository are some obsolete tests.*

### Utilities

For creating CArL data structure in unit tests, we refer to `carl-io/parser/Parser.h`.