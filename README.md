# SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox

## FMplex: A Novel Method for Solving Linear Real Arithmetic Problems

**Contact**

    Jasper Nalbach <nalbach@cs.rwth-aachen.de>, Valentin Promies <promies@cs.rwth-aachen.de>

## Instructions

### Install CArL

Install the CArL version from https://github.com/ths-rwth/carl/tree/pub/fmplex :

    sudo apt install bison flex
    git clone https://github.com/ths-rwth/carl.git -b pub/fmplex
    cd carl
    mkdir build
    cd build
    cmake ..
    make -j

For further instructions, see [CArL documentation](https://ths-rwth.github.io/carl/).

### Install SMT-RAT

    git clone https://github.com/ths-rwth/smtrat.git -b pub/fmplex
    cd smtrat
    mkdir build
    cd build
    cmake -DSMTRAT_DEVOPTION_Statistics=ON -DSMTRAT_Strategy=FMPlex/BTPruneBranchLevelPP ..
    make -j smtrat-static


For further instructions, see  [SMT-RAT documentation](https://ths-rwth.github.io/smtrat/).

Note that the solver variant is changed by setting the `SMTRAT_Strategy`option in CMake.

#### Strategies

Solver | Stragegy
---|---
Simplex | NoIncSimplex
FM | FouMoSolver
FMplex-MFO | FMPlex/BranchLevelPP
FMplex-MCL | FMPlex/MinColMinRowPP
FMplex-Rand | FMPlex/RandRandPP
FMplex-UB-MFO | FMPlex/PruneBranchLevelPP
FMplex-BT-MFO | FMPlex/BTPruneBranchLevelPP

### Benchmarks

Get the [QF_LRA benchmarks from SMT-LIB](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_LRA).
### Running SMT-RAT on a single instance

The following command will run SMT-RAT on `input.smt2` and print out statistics for the run:

    ./smtrat-static input.smt2 --stats.print

### Running SMT-RAT on the whole benchmark set

Build benchmax using 

    make benchmax

and run benchmax on all benchmarks in `/path/to/QF_LRA` with a timeout of `10m` and memory limit of `5Gi` and store the results (answers, running time, statistics) to `out.xml`:

    ./benchmax --statistics -T 10m -M 5Gi -S ./smtrat-static -D /path/to/QF_NRA -X out.xml -b local --use-tmp

Further instructions on running benchmax (i.e. running parallel jobs or using job management systems) in the [documentation](https://ths-rwth.github.io/smtrat/dd/d0f/benchmax.html).

## Results

The result XML files used in the paper are contained in `results/`. There, also a [Jupyter notebook](https://jupyter.org/) for evaluating the data is contained. For using them, you need to install the python package located at `utilities/benchmax/`: 

    pip3 install pandas matplotlib tikzplotlib numpy pillow
    cd ~/.local/lib/python3.8/site-packages/ # path to your python site-packages directory
    ln -s ~/src/smtrat/utilities/benchmax/ # path to the benchmax utility

For futher informaiton, see [here](https://ths-rwth.github.io/smtrat/dc/d44/benchmax-evaluation.html).

## Documentation

For more information, please checkout the docs.

* [SMT-RAT documentation](https://ths-rwth.github.io/smtrat/)
* [CArL documentation](https://ths-rwth.github.io/carl/) (SMT-RAT depends on [CArL](https://github.com/smtrat/carl) for formula and polynomial data structures and basic operations)
