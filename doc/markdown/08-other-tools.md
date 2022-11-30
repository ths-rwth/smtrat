# Other tools {#tools}

## Benchmarking

Alongside SMT-RAT, `benchmax` allows to easily run solvers on benchmarks and export the results.
See @subpage benchmax for more information.

## Delta debugging

**Delta debugging** describes a generic debugging approach based on automated testing.
Given a program and an input that provokes a certain behavior (for example an error) delta debugging is the process of iteratively changing the input, retaining the specific behavior. Usually, as the ultimate goal is a minimal example that triggers some bug by the application of a set of transformation rules.

*Note: Our legacy delta tool has been moved to [its own repository](https://github.com/ths-rwth/delta)*.

### Using ddSMT

Currently, we recommend using `ddSMT` as the state-of-the-art tool for delta debugging.

For a complete guide, we refer to the [documentation of ddSMT](https://ddsmt.readthedocs.io/).

Here, we give instructions for the most common use cases when developing with SMT-RAT. There are mainly two common scenarios where we use delta debugging: If there is a failing assertion or if SMT-RAT returns a wrong result. For these scenarios, we provide wrapper scripts preparing the input to ddsmt properly. 

First, install `ddSMT` and `z3`:
```bash
pip3 install ddsmt
sudo apt install z3
```

In case of a *failing assertion* on `in_file.smt2`, run
```bash
~/src/smtrat/utilities/ddsmt/ddsmt-assertion in_file.smt2 out_file.smt2 path_to_solver
```

In case SMT-RAT returns a *wrong result* on `in_file.smt2`, run
```bash
~/src/smtrat/utilities/ddsmt/ddsmt-wrong in_file.smt2 out_file.smt2 path_to_solver
```

## Analyzer

The `smtrat-analyzer` library can analyze static properties input formulas (such as number of variables, degrees, CAD projections, ...).

To use it from the CLI, build smtrat using `CLI_ENABLE_ANALYZER=ON` and `SMTRAT_DEVOPTION_Statistics=ON`. A single input file can be analyzed by running `./smtrat --analyze.enabled --stats.print input.smt2`; properties will be printed as statistics object, note that the solver will not be called. For further options, see `./smtrat --help`.

To collect properties of all formulas of a benchmark sets, the analyzer can be used with `benchmax`. To do so, specify add the binary as an `smtrat-analyzer` solver; for more information, see the `benchmax` subpage.

## Preprocessing

WIP