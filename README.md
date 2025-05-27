# SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox

Online Resource associated with the paper

    "Solving Non-Linear Optimization with the Cylindrical Algebraic Covering Method"
    Valentin Promies <promies@cs.rwth-aachen.de>, Erika Ábrahám <abraham@cs.rwth-aachen.de>

## Building the Configurations used in the Paper

Building the provided Dockerfile will create an image containing the three variants of SMT-RAT used in the paper.

## Generating Benchmarks, Stats and Figures

The `artifact` directory contains additional material:

* `generate_benchmarks.py`: a python script for generating the benchmarks used in the paper from the QF_NRA set from SMT-LIB. To run the script, you have to have the SMT-LIB set present (can be obtained [from Zenodo](https://doi.org/10.5281/zenodo.11061097)), and you need to adapt some variables in the scripts containing the paths for the benchmark sets. This script uses `qfnra.diff` and `qfnra_hard.diff` which specify the objective function for each file.
* `stats-opt-*.csv` are csv files containing our collected data.
* `analyse.ipynb` is a jupyter notebook showing how to use the csv files to obtain the numbers and plots from the paper.


# General SMT-RAT Documentation

SMT-RAT is a modular SMT solver with strong focus on non-linear real arithmetic, and basic support for quantifier elimination. Its main scope is the implemention and evaluation of methods developed at the Theory of Hybrid Systems group at RWTH Aachen University. 

It is SMT-LIB 2 compliant, however, some methods are not adapted for the incremental interface of SMT-LIB. 

## Supported Theories and Implemented Methods (excerpt)

### SMT

* `QF_LRA`: Simplex, FMplex
* `QF_NRA`: Subtropical Satisfiability, MCSAT (with Fourier-Motzkin, Virtual Substitution, Interval Constraint Propagation, CAD/Single Cell Construction), DPLL(Virtual Substitution, Interval Constraint Propagation, Cylindrical Algebraic Coverings, Cylindrical Algebraic Decomposition), Cylindrical Algebraic Coverings (standalone)
* `NRA`: Cylindrical Algebraic Coverings (standalone)
* `QF_NIA` / `QF_NIRA`: Bit-blasting, Branch&Bound 

### Quantifier Elimination

* `LRA`: FMplex, Fourier-Motzkin (conjunctions only)
* `NRA`: CAlC

## Reporting Bugs

We are grateful for bug reports, 
Please use our issue tracker.

## User and Developer Documentation

Please check out the documentation for building and installation instructions, as well as documentation of the code.

* [SMT-RAT documentation](http://ths-rwth.github.io/smtrat)
* [CArL documentation](http://ths-rwth.github.io/carl) (SMT-RAT depends on [CArL](https://github.com/ths-rwth/carl) for formula and polynomial data structures and basic operations)

## Contact

* Jasper Nalbach <nalbach@cs.rwth-aachen.de>
* Valentin Promies <promies@cs.rwth-aachen.de>