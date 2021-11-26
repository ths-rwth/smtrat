## Checkpoints {#checkpoints}

Checkpoints are useful for debugging a run of SMT-RAT, i.e. if an implementation of SMT-RAT behaves the same as some other implementation or some pseudocode.

To do so, we can insert checkpoints with a channel, a name, and a list of arguments of arbitrary type into the code. During a run, a sequence of checkpoints is produced which represent a run of the algorithm. We then can specify test cases which set up a reference run and then start the solver on an according input. SMT-RAT will then check during this run whether all checkpoints are hit in the correct order and will give output on that.

### Enabling this feature

You need to turn on the CMake option `SMTRAT_DEVOPTION_Checkpoints`.

### Specyfing checkpoints

Insert 

    SMTRAT_CHECKPOINT("channel_name", "checkpoint_name", parameter1, parameter2, ...);

into the code.

### Setting up a reference run

Create a test case in `src/test`. Include `#include <smtrat-common/smtrat-common.h>` and add checkpoints using

    SMTRAT_ADD_CHECKPOINT("channel_name", "checkpoint_name", false, parameter1, parameter2, ...)

or

    SMTRAT_ADD_CHECKPOINT("channel_name", "checkpoint_name", true, parameter1, parameter2, ...)

to assert that a checkpoint is reached.

Afterwards, run the respective SMT-RAT code.

You can clear all checkpoints of a channel using

    SMTRAT_CLEAR_CHECKPOINT("channel_name");

to reset a channel, that is, removing all checkpoints and resetting the pointer.