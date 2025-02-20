# SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox

Online Resource associated with the paper

    Projective Delineability for Single Cell Construction
    Jasper Nalbach <nalbach@cs.rwth-aachen.de> (RWTH Aachen University), Lucas Michel (University of Liège), Erika Ábrahám (RWTH Aachen University), Christopher W. Brown (United States Naval Academy), James H. Davenport (University of Bath), Matthew England (Coventry University), Pierre Mathonet (University of Liège), Naïm Zénaïdi (University of Liège)

## Instructions for Running the Experiments

### Install SMT-RAT

    git clone https://github.com/ths-rwth/smtrat.git -b pub/pdel-scc
    cd smtrat
    mkdir build
    cd build
    cmake -DSMTRAT_DEVOPTION_Statistics=ON -DSMTRAT_Strategy=Default ..
    make -j smtrat-static


For further instructions, see  [SMT-RAT documentation](http://smtrat.github.io/).

Note that the solver variant is changed by setting the `SMTRAT_Strategy` option in CMake.

### Benchmarks

Get the [QF_NRA benchmarks from SMT-LIB](https://zenodo.org/records/11061097/files/QF_NRA.tar.zst?download=1).

### Running SMT-RAT's variants 

The following command will run SMT-RAT on `input.smt2` and print out statistics for the run:

    ./smtrat-static input.smt2 --stats.print

We do not provide scripts here for running all experiments, as the way this step heavily depends on the user's system.

You may use our benchmarking tool [benchmax](https://github.com/ths-rwth/benchmax-py).

#### Strategies

The following strategies can be chosen (by setting the `SMTRAT_Strategy` option in CMake) to compile the solvers from the paper:

Solver | Strategy
---|---
BC            | MCSAT/OCNewBC
LDB           | MCSAT/OCNewLDB
BC-PDEL       | MCSAT/OCNewBCpdel
LDB-PDEL      | MCSAT/OCNewLDBpdel

## Evaluation

The `evaluation.zip` contains `csv` files with the results for each solver and benchmark, as well as two Jupyter notebooks to reproduce the figures and tables from the paper. To run the Jupyter notebooks, you need to install a small [python package](https://ths-rwth.github.io/smtrat/dc/d44/benchmax-evaluation.html) delivered with SMT-RAT:

    pip3 install pandas matplotlib numpy pillow

    cd ~/.local/lib/python3.9/site-packages/ # path to your python site-packages directory
    ln -s ~/src/smtrat/utilities/benchmax/ # path to the benchmax utility


## Documentation

For more information, please check out the docs.

* [SMT-RAT documentation](http://ths-rwth.github.io/smtrat)
* [CArL documentation](http://ths-rwth.github.io/carl) (SMT-RAT depends on [CArL](https://github.com/ths-rwth/carl) for formula and polynomial data structures and basic operations)

