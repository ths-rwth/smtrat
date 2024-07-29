# SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox

**Contact**

    Jasper Nalbach <nalbach@cs.rwth-aachen.de>

## Instructions for Running the Experiments

### Install SMT-RAT

    git clone https://github.com/ths-rwth/smtrat.git -b pub/covering-journal
    cd smtrat
    mkdir build
    cd build
    cmake -DSMTRAT_DEVOPTION_Statistics=ON -DSMTRAT_Strategy=Default -D CLI_ENABLE_QUANTIFIER_ELIMINATION=ON ..
    make -j smtrat-static


For further instructions, see  [SMT-RAT documentation](http://smtrat.github.io/).

Note that the solver variant is changed by setting the `SMTRAT_Strategy` option in CMake.

### Benchmarks

Get the [QF_NRA benchmarks from SMT-LIB](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_NRA) and the [NRA benchmarks from SMT-LIB](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/NRA).

Bath benchmarks: The `qe-benchmarks` folder in this repository contains a Python script which downloads the examples from <https://researchdata.bath.ac.uk/69/> and converts them to SMT-LIB. Instructions:
* Install [Tarski 1.28](https://www.usna.edu/Users/cs/wcbrown/tarski/)
* Set `tarski_path` in `smtlib_from_qepcad.py`
* Run `bath_to_smtlib.py`
The resulting benchmarks are contained in `qe-benchmarks/smtlib`.


### Running SMT-RAT's variants 

The following command will run SMT-RAT on `input.smt2` and print out statistics for the run:

    ./smtrat-static input.smt2 --stats.print

We do not provide scripts here for running all experiments, as the way this step heavily depends on the user's system. Our evaluation tool is documented [here](https://smtrat.github.io/dd/d0f/benchmax.html).

#### Strategies

The following strategies can be chosen (by setting the `SMTRAT_Strategy` option in CMake) to compile the solvers from the paper:

##### Default SMT-RAT Strategy

Solver | Strategy
---|---
SMT-RAT | Default

##### Evaluation of Variants

Solver | Strategy
---|---
Variable Ordering: Feature Based            | CoveringNG/PPVarorderPickering
Variable Ordering: Max Univariate           | CoveringNG/PPVarorderUnivariate (same as CoveringNG/PPDefault)
Boolean Reasoning: Evaluation               | CoveringNG/PPBooleanOff
Boolean Reasoning: Propagation              | CoveringNG/PPBooleanPropagation (same as CoveringNG/PPDefault)
Boolean Reasoning: Exploration              | CoveringNG/PPBooleanExploration
Implicant Selection: Size                   | CoveringNG/PPImplicantsSizeOnly
Implicant Selection: Feature Based          | CoveringNG/PPImplicantsPickeringTotal
Implicant Selection: Sum of Total Degrees   | CoveringNG/PPImplicantsSotd (same as CoveringNG/PPDefault)
Implicant Selection: Reverse Sotd           | CoveringNG/PPImplicantsSotdReverse
Preprocessing: Off                          | CoveringNG/PPDefault
Preprocessing: Gröbner bases                | CoveringNG/PPInprocessingOn

##### Comparison with Other Solvers

Solver | Strategy
---|---
MCSAT                   | MCSAT/PPDefault
MCSAT-OC                | MCSAT/PPOCNew
CAlC (quantifier-free)  | CoveringNG/PPDefault
CAlC (quantifiers)      | CoveringNG/Default

##### Comparison with Other Quantifier Elimination Tools

There are no strategies for quantifier elimination. Instead, quantifier elimination needs to be enabled by setting the `CLI_ENABLE_QUANTIFIER_ELIMINATION` CMake option to `ON`. Then, the quantifier elimination method is specified via the command line by passing the `--qe-method covering` option.

### Running QEPCAD B/Tarski and Redlog/Reduce

The `qe-wrapper` directory of this repository contains wrapper Python scripts for running QEPCAD B and Redlog on benchmarks in SMT-LIB format. Instructions:
* Install [Tarski 1.28](https://www.usna.edu/Users/cs/wcbrown/tarski/) 
* Set `tarski_path` in `tarski_wrapper.py`
* Install [Redlog](https://sourceforge.net/projects/reduce-algebra/files/snapshot_2023-12-18/linux64/)
* `pip3 install pysmt`
* Run `tarski_wrapper.py <input.smt2>` or `tarski_wrapper.py <input.smt2>`. The scripts will return either `sat` or `unsat` on SMT benchmarks; or the number of atoms, disjunctions and conjunctions of the solution formula on QE benchmarks. In case the backend is incomplete, it may return `unknown`; if some benchmark uses unsupported features (e.g. division by a non-constant), the scripts will return an error as well.

## Evaluation

The `evaluation.zip` contains `csv` files with the results for each solver and benchmark, as well as two Jupyter notebooks to reproduce the figures and tables from the paper. To run the Jupyter notebooks, you need to install a small [python package](https://ths-rwth.github.io/smtrat/dc/d44/benchmax-evaluation.html) delivered with SMT-RAT:

    pip3 install pandas matplotlib tikzplotlib numpy pillow

    cd ~/.local/lib/python3.8/site-packages/ # path to your python site-packages directory
    ln -s ~/src/smtrat/utilities/benchmax/ # path to the benchmax utility


## Documentation

For more information, please check out the docs.

* [SMT-RAT documentation](http://ths-rwth.github.io/smtrat)
* [CArL documentation](http://ths-rwth.github.io/carl) (SMT-RAT depends on [CArL](https://github.com/ths-rwth/carl) for formula and polynomial data structures and basic operations)

