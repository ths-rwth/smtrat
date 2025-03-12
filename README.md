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

## Getting Started

### Installation

* Clone this repository, or download and extract the latest release
* `cd smtrat`
* `mkdir build && cd build`
* `sudo apt install cmake-ncurses-gui g++ libboost-all-dev cmake make libgmp-dev libgtest-dev` Make sure you have installed the dependencies
  * see [the documentation for details](https://ths-rwth.github.io/smtrat/d5/dfc/installation.html)
* `cmake ..`
* Set variables using `ccmake ..`
  * `SMTRAT_Strategy`: The SMT-RAT Strategy; if you do not know what this is, leave it to `Default`
  * `CLI_ENABLE_QUANTIFIER_ELIMINATION`: If you want to use **quantifier elimination**, you need to set this variable to `ON`.
* `make -jx smtrat` (where `x` is the number of cores)
  * Note that the build process needs an internet connection to download additional dependencies.

### Usage

#### SMT

SMT-RAT reads SMT-LIB files. We provide some example files: The first two are quantifier-free, the last one contains quantifiers.

```
./smtrat-shared doc/examples/qfnra-sat.smt2
./smtrat-shared doc/examples/qfnra-unsat.smt2
./smtrat-shared doc/examples/nra-sat.smt2
```

You may use the `(get-model)` command to obtain a solution if `(check-sat)` returned `sat`.

#### Quantifier Elimination

The inputs are SMT-LIB files which use the `(apply qe)` command instead of `(check-sat)` (following the `z3` syntax). Non-quantified variables are treated as parameters.

```
./smtrat-shared doc/examples/qe.smt2
```

SMT-RAT returns teh quantifier elimination result in SMT-LIB format. 
Note that the output may contain *indexed root expressions* of the form `(root p i x)` where `p` is a multivariate polynomial, `k` a positive integer, and `x` a variable. These expressions are functions that map an assignment of variables other than `x` to the `k`th root of `p` in `x`.

You can use these expressions in the input to SMT-RAT (for now, only as part of qunatifier-free formulas) to reason about them.


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