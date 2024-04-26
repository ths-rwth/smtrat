# SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox

**Contact**

    Jasper Nalbach <nalbach@cs.rwth-aachen.de>

## Instructions for Running the Experiments

### Install SMT-RAT

    git clone https://github.com/ths-rwth/smtrat.git -b pub/irrelevant-roots
    cd smtrat
    mkdir build
    cd build
    cmake -DSMTRAT_DEVOPTION_Statistics=ON -DSMTRAT_Strategy=Filter/BCNoop ..
    make -j smtrat-static


For further instructions, see  [SMT-RAT documentation](http://smtrat.github.io/).

Note that the solver variant is changed by setting the `SMTRAT_Strategy` option in CMake.

### Benchmarks

Get the [non-incremental QF_NRA benchmarks from the 2023 SMT-LIB release](https://zenodo.org/records/10607722).

### Running SMT-RAT variants 

The following command will run SMT-RAT on `input.smt2` and print out statistics for the run:

    ./smtrat-static input.smt2 --stats.print

We do not provide scripts here for running all experiments, as the way this step heavily depends on the user's system. Our evaluation tool is documented [here](https://smtrat.github.io/dd/d0f/benchmax.html).

#### Strategies

The following strategies can be chosen (by setting the `SMTRAT_Strategy` option in CMake) to compile the solvers from the paper:


##### Evaluation of Variants

Solver | Strategy
---|---
Baseline | Filter/BCNoop
All | Filter/BCAll
Independent | Filter/BCIrredIndep
Rational | Filter/BCRational
Bounds | Filter/BCBoundsOnly

## Evaluation

The `evaluation.zip` contains `csv` files with the results for each solver and benchmark, as well as two Jupyter notebooks to reproduce the figures and tables from the paper. To run the Jupyter notebooks, you need to install a small [python package](https://ths-rwth.github.io/smtrat/dc/d44/benchmax-evaluation.html) delivered with SMT-RAT:

    pip3 install pandas matplotlib tikzplotlib numpy pillow

    cd ~/.local/lib/python3.8/site-packages/ # path to your python site-packages directory
    ln -s ~/src/smtrat/utilities/benchmax/ # path to the benchmax utility


## Documentation

For more information, please check out the docs.

* [SMT-RAT documentation](http://ths-rwth.github.io/smtrat)
* [CArL documentation](http://ths-rwth.github.io/carl) (SMT-RAT depends on [CArL](https://github.com/ths-rwth/carl) for formula and polynomial data structures and basic operations)
