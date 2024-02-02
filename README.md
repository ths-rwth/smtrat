# SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox

## A Divide-and-Conquer Approach to Variable Elimination in Linear Real Arithmetic

**Contact**

    Valentin Promies <promies@cs.rwth-aachen.de>

## Instructions

### Install CArL

Install CArL version 24.02 from https://github.com/ths-rwth/carl/tree/24.02 :  TODO

    sudo apt install bison flex
    git clone https://github.com/ths-rwth/carl.git --branch 24.02
    cd carl
    mkdir build
    cd build
    cmake ..
    make -j

For further instructions, see [CArL documentation](https://ths-rwth.github.io/carl/).

### Install SMT-RAT

    git clone https://github.com/ths-rwth/smtrat.git -b pub/fmplex-qe
    cd smtrat
    mkdir build
    cd build
    cmake -DSMTRAT_DEVOPTION_Statistics=ON -DCLI_ENABLE_QUANTIFIER_ELIMINATION=ON ..
    make -j smtrat-static


For further instructions, see  [SMT-RAT documentation](https://ths-rwth.github.io/smtrat/).

The code related to the paper can be found in `src/smtrat-qe/fmplex`

### Benchmarks

The benchmarks considered in the paper are available [on Zenodo](https://zenodo.org/records/10605373).

### Running SMT-RAT on a single instance

The following command will run SMT-RAT on `input.smt2` using the FMplex variable elimination and print out statistics for the run:

    ./smtrat-static input.smt2 --stats.print --module.parameter qe-method=fmplex

## Results

CSV files with the results used in the paper are contained in `fmplex-qe-results/`. There, also a [Jupyter notebook](https://jupyter.org/) for evaluating the data is contained. 

## Documentation

For more information, please checkout the docs.

* [SMT-RAT documentation](https://ths-rwth.github.io/smtrat/)
* [CArL documentation](https://ths-rwth.github.io/carl/) (SMT-RAT depends on [CArL](https://github.com/smtrat/carl) for formula and polynomial data structures and basic operations)