# SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox

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