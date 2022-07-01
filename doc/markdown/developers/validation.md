## Validation {#validation}

For debugging purposes, it can be useful to verify intermediate results (explanations, lemmas, etc) using an external SMT solver. SMT-RAT allows to store formulas during the solving process which are written to a `smt2` file once the solving process is finished.

### Enabling this feature

For enabling this feature, the `SMTRAT_DEVOPTION_Validation` needs to be turned on in the CMake settings.

### Logging formulas

The API allows to create a *validation point* with a given channel and a name. The channel and name should identify the validation point uniquely. The channel (e.g. `smtrat.modules.vs`) can be used to turn on and off validation points (similarly to logging channels) while the name (e.g. `substitution_result`) further distinguishes validation points within a channel.

To initialize a validation point with channel and name and store its reference to a variable, use

    SMTRAT_VALIDATION_INIT(channel, variable);

Hint: to put it in a static variable, use

    SMTRAT_VALIDATION_INIT_STATIC(channel, variable);

To an initialized validation point stored in a variable, we can add a formula to be assumed to be satisfiable (consistent = true) or unsatisfiable (consistent = false). Each formula added to a validation point gets a unique index (given incrementally), which is also logged in the given channel with debug level.

    SMTRAT_VALIDATION_ADD_TO(variable, name, formula, consistent);

To combine the two steps above, use:

    SMTRAT_VALIDATION_ADD(channel, name, formula, consistent);

### Command line usage

By appending the command line parameter `--validation.export-smtlib`, the formulas are stored to an smtlib file (by default `validation.smt2`, can be customized using `--validation.smtlib-filename`).

Note that all channels of interest need to be activated explicitly with  `--validation.channel channel1 --validation.channel channel2 ...`. Furthermore, `--validation.channel path.to` will activate all channels starting with `path.to`, i.e. `path.to.channel1`, `path.to.channel2` etc.

### Segmentation faults

Note that the formulas are only written to a file if smtrat terminates without an segmentation fault. If there is an assertion failing, set `DEVELOPER=OFF` in cmake. 