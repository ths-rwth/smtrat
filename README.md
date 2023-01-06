# SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox

## Subtropical Satisfiability for SMT Solving

**Contact**

    Jasper Nalbach <nalbach@cs.rwth-aachen.de>

## Instructions

### Install CArL

Install the CArL version from https://github.com/ths-rwth/carl/tree/pub/subtropical :

    sudo apt install bison flex
    git clone https://github.com/ths-rwth/carl.git -b pub/subtropical
    cd carl
    mkdir build
    cd build
    cmake ..
    make -j

For further instructions, see [CArL documentation](http://smtrat.github.io/carl).

### Install SMT-RAT

    git clone https://github.com/ths-rwth/smtrat.git -b pub/subtropical
    cd smtrat
    mkdir build
    cd build
    cmake -DSMTRAT_DEVOPTION_Statistics=ON -DSMTRAT_Strategy=STrop/Formula ..
    make -j smtrat-static


For further instructions, see  [SMT-RAT documentation](http://smtrat.github.io/).

Note that the solver variant is changed by setting the `SMTRAT_Strategy` option in CMake.

### Benchmarks

Get the [QF_NRA benchmarks from SMT-LIB](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_NRA).

### Running SMT-RAT's subtropical variants 

The following command will run SMT-RAT on `input.smt2` and print out statistics for the run:

    ./smtrat-static input.smt2 --stats.print

We do not provide scripts here for running all experiments, as the way this step heavily depends on the user's system. Own evaluation tool is documented [here](https://smtrat.github.io/dd/d0f/benchmax.html).

#### Strategies

The following strategies can be chosen (by setting the `SMTRAT_Strategy` option in CMake) to compile the solvers from the paper:

Solver | Strategy
---|---
Equation | STrop/TransformationEQ
Formula | STrop/Formula
FormulaAux | STrop/FormulaAlt
Incremental | STrop/Incremental
CAlC | STrop/CADBackendsOnly
I+CAlC | STrop/IncrementalWCADBackends
F+CAlC | STrop/FormulaWCADBackends
FA+CAlC | STrop/FormulaAltWCADBackends
F+I+CAlC | STrop/FormulaWCADBackendsFull
FA+I+CAlC | STrop/FormulaAltWCADBackendsFull

### Apply the transformation as preprocessing for another solver

For applying the transformation only in order to run Z3 or cvc5 on the transformation result, follow these steps:

1. Compile SMT-RAT using the `STrop/FormulaOutputOnly` strategy and set the CMake option `SMTRAT_DEVOPTION_Validation` to `ON`.
2. Adapt `benchmark_directory`, `out_directory`, `solver` and `threads` in the `transformation.py` script provided in the root directory of this repository.
3. Run the script. It will apply the transformation on all benchmarks in `benchmark_directory`, store it to `out_directory` (preserving the directory structure and names) using the `solver`.
4. Run any linear solver on the transformation results. Note that if the transformation could not be applied, the corresponding transformation result files do not contain any formula (hence the solver will not to anything). If the subtropical method fails, the solver will return `unsat` on the transformed instance. If it finds a satisfying solution, the solver returns `sat`.

## Documentation

For more information, please checkout the docs.

* [SMT-RAT documentation](http://smtrat.github.io/)
* [CArL documentation](http://smtrat.github.io/carl) (SMT-RAT depends on [CArL](https://github.com/smtrat/carl) for formula and polynomial data structures and basic operations)
