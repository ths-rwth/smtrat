# SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox

Online Resource associated with the paper

    A Variant of Non-uniform Cylindrical Algebraic Decomposition for Real Quantifier Elimination
    Jasper Nalbach <nalbach@cs.rwth-aachen.de> (RWTH Aachen University), Erika Ábrahám (RWTH Aachen University)

## Instructions for Running the Experiments

### Install SMT-RAT

    git clone https://github.com/ths-rwth/smtrat.git -b pub/nucad
    cd smtrat
    mkdir build
    cd build
    cmake -D CLI_ENABLE_QUANTIFIER_ELIMINATION=ON -D SMTRAT_DEVOPTION_Statistics=ON -D SMTRAT_Strategy=Default -D SMTRAT_Settings_QE_CAlC=EvalPBcldboundsSettings -D SMTRAT_Settings_QE_NuCAD=EvalPBcldboundsSettings ..
    make -j smtrat-static

For further instructions, see  [SMT-RAT documentation](http://smtrat.github.io/).

### Benchmarks

* SMT-LIB QF_NRA and NRA benchmarks: https://doi.org/10.5281/zenodo.11061097
  * [QF_NRA](https://zenodo.org/records/11061097/files/QF_NRA.tar.zst?download=1).
  * [NRA](https://zenodo.org/records/11061097/files/NRA.tar.zst?download=1).
* Bath QE benchmarks: `qe-benchmarks` folder from https://doi.org/10.5281/zenodo.14355422


### Building and Running SMT variants

The following strategies can be chosen (by setting the `SMTRAT_Strategy` option in CMake) to compile the solvers from the paper:

Solver | Strategy
---|---
NuCAD            | Eval/NucadPBcldbounds
CAlC             | Eval/CAlCPBcldbounds

The following command will run SMT-RAT on `input.smt2` and print out statistics for the run:

    ./smtrat-static input.smt2 --stats.print

### Building and Running QE variants


Build SMT-RAT as described above. The settings will already select the correct variants.

To run qunatifier elimination, the input file should use the `(apply qe)` command instead of `(check-sat)`. Thus, to run quantifier elimination on the QF_NRA set, you need to replace `(check-sat)` by `(apply qe)` e.g. using:

    find ./ -type f -exec sed -i 's/(check-sat)/(apply\ qe)/g' {} \;

The following command will run CAlC on `input.smt2` and print out statistics for the run:

    ./smtrat-static input.smt2 --stats.print --qe-method covering

The following command will run NuCAD on `input.smt2` and print out statistics for the run:

    ./smtrat-static input.smt2 --stats.print --qe-method nucad


### Running QEPCAD B/Tarski and Redlog/Reduce

The `qe-tools-wrapper` directory of this repository contains wrapper Python scripts for running QEPCAD B and Redlog on benchmarks in SMT-LIB format. Instructions:
* Install [Tarski 1.28](https://www.usna.edu/Users/cs/wcbrown/tarski/) 
* Set `tarski_path` in `tarski_wrapper.py`
* Install [Redlog](https://sourceforge.net/projects/reduce-algebra/files/snapshot_2023-12-18/linux64/)
* `pip3 install pysmt`
* Run `tarski_wrapper.py <input.smt2>` or `tarski_wrapper.py <input.smt2>`. The scripts will return either `sat` or `unsat` on SMT benchmarks; or the number of atoms, disjunctions and conjunctions of the solution formula on QE benchmarks. In case the backend is incomplete, it may return `unknown`; if some benchmark uses unsupported features (e.g. division by a non-constant), the scripts will return an error as well.

## Verification of Solution Formulas

The solution formulas of SMT-RAT are verified as follows, using the scripts in the `qe-tools-wrapper` directory:
* Install [Tarski 1.40](https://github.com/chriswestbrown/tarski/tree/2e16a504f97fb6c8736ed9126d3e0b696ebbf683) 
* Set `tarski_path` in `tarski_wrapper.py`
* `pip3 install pysmt`
* Adapt `smtrat-nucad.sh` or `smtrat-calc.sh` to contain the path to the SMT-RAT binary.
* Run `verify_qe_result.py smtrat-nucad.sh ./tarski_wrapper.py ../qe-benchmarks/smtlib/` or `verify_qe_result.py smtrat-calc.sh ./tarski_wrapper.py ../qe-benchmarks/smtlib/`. Some instances may not be verified due to a timeout of SMT-RAT or Tarski; you can increase this time limit in the `verify_qe_result.py` script.


### Batch Execution

We do not provide scripts here for running all experiments, as the way this step heavily depends on the user's system.

You may use our benchmarking tool [benchmax](https://github.com/ths-rwth/benchmax-py).

## Evaluation

The `evaluation.zip` contains `csv` files with the results for each solver and benchmark, as well as two Jupyter notebooks to reproduce the figures and tables from the paper. To run the Jupyter notebooks, you need to install a small python package (usage instructions [here](https://github.com/ths-rwth/benchmax-py/blob/main/examples/inspection-example.ipynb)):

    pip3 install pandas matplotlib numpy pillow

    cd ~/.local/lib/python3.9/site-packages/ # path to your python site-packages directory
    ln -s ~/src/smtrat/utilities/benchmax/ # path to the benchmax utility


## Documentation

For more information, please check out the docs.

* [SMT-RAT documentation](http://ths-rwth.github.io/smtrat)
* [CArL documentation](http://ths-rwth.github.io/carl) (SMT-RAT depends on [CArL](https://github.com/ths-rwth/carl) for formula and polynomial data structures and basic operations)