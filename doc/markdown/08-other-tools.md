# Other tools {#tools}

## Delta debugging

*Note: Our legacy delta tool has been moved to [its own repository](https://github.com/ths-rwth/delta)*.

## Analyzer

The `smtrat-analyzer` library can analyze static properties input formulas (such as number of variables, degrees, CAD projections, ...).

To use it from the CLI, build smtrat using `CLI_ENABLE_ANALYZER=ON` and `SMTRAT_DEVOPTION_Statistics=ON`. A single input file can be analyzed by running `./smtrat --analyze.enabled --stats.print input.smt2`; properties will be printed as statistics object, note that the solver will not be called. For further options, see `./smtrat --help`.

## Preprocessing

WIP