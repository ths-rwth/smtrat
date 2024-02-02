# SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox

**Contact**

    Jasper Nalbach <nalbach@cs.rwth-aachen.de>

## Instructions for Running the Experiments

### Install SMT-RAT

    git clone https://github.com/ths-rwth/smtrat.git -b pub/covering-implementation
    cd smtrat
    mkdir build
    cd build
    cmake -DSMTRAT_DEVOPTION_Statistics=ON -DSMTRAT_Strategy=Default ..
    make -j smtrat-static


For further instructions, see  [SMT-RAT documentation](http://smtrat.github.io/).

Note that the solver variant is changed by setting the `SMTRAT_Strategy` option in CMake.

### Benchmarks

Get the [QF_NRA benchmarks from SMT-LIB](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_NRA) and the [NRA benchmarks from SMT-LIB](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/NRA).

### Running SMT-RAT's variants 

The following command will run SMT-RAT on `input.smt2` and print out statistics for the run:

    ./smtrat-static input.smt2 --stats.print

We do not provide scripts here for running all experiments, as the way this step heavily depends on the user's system. Our evaluation tool is documented [here](https://smtrat.github.io/dd/d0f/benchmax.html).

#### Strategies

The following strategies can be chosen (by setting the `SMTRAT_Strategy` option in CMake) to compile the solvers from the paper:

##### Evaluation of Variants

Solver | Strategy
---|---
Variable Ordering: Feature Based            | CoveringNG/PPVarorderPickering
Variable Ordering: Max Univariate           | CoveringNG/PPVarorderUnivariate
Boolean Reasoning: Evaluation               | CoveringNG/PPBooleanOff
Boolean Reasoning: Propagation              | CoveringNG/PPBooleanPropagation
Boolean Reasoning: Exploration              | CoveringNG/PPBooleanExploration
Implicant Selection: Size                   | CoveringNG/PPImplicantsSizeOnly
Implicant Selection: Feature Based          | CoveringNG/PPImplicantsPickeringTotal
Implicant Selection: Sum of Total Degrees   | CoveringNG/PPImplicantsSotd
Implicant Selection: Reverse Sotd           | CoveringNG/PPImplicantsSotdReverse

##### Comparison with Other Solvers

Solver | Strategy
---|---
MCSAT                   | MCSAT/PPDefault
MCSAT-OC                | MCSAT/PPOCNew
CAlC (quantifier-free)  | CoveringNG/PPDefault
CAlC (quantifiers)      | CoveringNG/Default

##### Default SMT-RAT Strategy

Solver | Strategy
---|---
SMT-RAT | Default

## Evaluation

The `evaluation.zip` contains `csv` files with the results for each solver and benchmark, as well as two Jupyter notebooks to reproduce the figures and tables from the paper. To run the Jupyter notebooks, you need to install a small [python package](https://ths-rwth.github.io/smtrat/dc/d44/benchmax-evaluation.html) delivered with SMT-RAT:

    pip3 install pandas matplotlib tikzplotlib numpy pillow

    cd ~/.local/lib/python3.8/site-packages/ # path to your python site-packages directory
    ln -s ~/src/smtrat/utilities/benchmax/ # path to the benchmax utility


## Documentation

For more information, please check out the docs.

* [SMT-RAT documentation](http://ths-rwth.github.io/smtrat)
* [CArL documentation](http://ths-rwth.github.io/carl) (SMT-RAT depends on [CArL](https://github.com/ths-rwth/carl) for formula and polynomial data structures and basic operations)
