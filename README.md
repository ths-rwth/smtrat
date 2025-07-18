# SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox

Online Resource associated with the dissertation

    Cylindrical Algebraic Decomposition Based Methods in Satisfiability Modulo Non-linear Real Arithmetic
    Jasper Nalbach <nalbach@cs.rwth-aachen.de> (RWTH Aachen University)

## Instructions for Running the Experiments

### Installing SMT-RAT

    git clone https://github.com/ths-rwth/smtrat.git -b pub/dissertation-nalbach
    cd smtrat
    mkdir build
    cd build
    cmake -DCLI_ENABLE_QUANTIFIER_ELIMINATION=ON -DSMTRAT_DEVOPTION_Statistics=ON -DSMTRAT_Strategy=Default ..
    make -j smtrat-static


This will also install the requried version of CArL 25.04, which is also available at <https://zenodo.org/records/15464618>.

For further instructions, see  [SMT-RAT documentation](http://smtrat.github.io/).

Note that the solver variant is changed by setting the `SMTRAT_Strategy` option in CMake.

### Running SMT-RAT's variants 

The following command will run SMT-RAT on `input.smt2` and print out statistics for the run:

    ./smtrat-static input.smt2 --stats.print

To run qunatifier elimination, the input file should use the `(apply qe)` command instead of `(check-sat)`.

The following command will run CAlC on `input.smt2` and print out statistics for the run:

    ./smtrat-static input.smt2 --stats.print --qe-method covering

The following command will run NuCAD on `input.smt2` and print out statistics for the run:

    ./smtrat-static input.smt2 --stats.print --qe-method nucad

#### Strategies

**SMT Variants:** The following strategies can be chosen by setting the `SMTRAT_Strategy` option in CMake to compile the SMT variants from the paper. *Important: This setting only affects the SMT solver. For quantifier elimination, a different setting as shown below needs to be adapted!*

Solver | Strategy
---|---
SMT-RAT | Default
CAlC-Inc | Eval/CalcInc
CAlC | Eval/Calc
CAlC\<Eval\> | Eval/CalcEval
CAlC\<FullCov\> | Eval/CalcFull
CAlC\<Noop\> | Eval/CalcNoop
CAlC\<Noop,FullCov\> | Eval/CalcNoopFull
NuCAD | Eval/Nucad
MCSAT-Comb | Eval/McsatComb
MCSAT / MCSAT\<Bc,BcCov\> | Eval/Mcsat
MCSAT\<Chain,ChainCov\> | Eval/McsatPChain
MCSAT\<Compound,CompoundCov\> | Eval/McsatPCompound
MCSAT\<Full,FullCov\> | Eval/McsatPFull
MCSAT\<Ldb,LdbCov\> | Eval/McsatPLdb
MCSAT\<VSIDS\> / MCSAT\<VSIDS,Bc,BcCov\> | Eval/McsatVsids
MCSAT\<VSIDS,Chain,ChainCov\> | Eval/McsatVsidsPChain
MCSAT\<VSIDS,Compound,CompoundCov\> | Eval/McsatVsidsPCompound
MCSAT\<VSIDS,Full,FullCov\>  | Eval/McsatVsidsPFull
MCSAT\<VSIDS,Ldb,LdbCov\> | Eval/McsatVsidsPLdb
MCSAT\<OptDegree,BcCov\> | Eval/McsatPOptdegree
MCSAT\<OptNumRes,BcCov\> | Eval/McsatPOptnumres
MCSAT\<OptNumVar,BcCov\> | Eval/McsatPOptnumvar
MCSAT\<OptSOTD,BcCov\> | Eval/McsatPOptsotd
MCSAT\<VSIDS,OptDegree,BcCov\> | Eval/McsatVsidsPOptdegree
MCSAT\<ApxConst,BcCov\> | Eval/McsatPApxconst
MCSAT\<ApxPwl3,BcCov\> | Eval/McsatPApxpwl2
MCSAT\<ApxPwl5,BcCov\> | Eval/McsatPApxpwl4
MCSAT\<ApxPwl7,BcCov\> | Eval/McsatPApxpwl6
MCSAT\<VSIDS,ApxConst,BcCov\> | Eval/McsatVsidsPApxconst
MCSAT\<BcLdAll,BcLdAllCov\> | Eval/McsatPBcldall
MCSAT\<BcLdBounds,BcLdBoundsCov\> | Eval/McsatPBcldbounds
MCSAT\<BcLdIndep,BcLdIndepCov\> | Eval/McsatPBcldindep
MCSAT\<BcLdRat,BcLdRatCov\> | Eval/McsatPBcldrat
MCSAT\<BcPd,BcPdCov\> | Eval/McsatPBcpd
MCSAT\<LdbPd,LdbPdCov\> | Eval/McsatPLdbpd
MCSAT\<VSIDS,BcPd,BcPdCov\> | Eval/McsatVsidsPBcpd
MCSAT\<VSIDS,LdbPd,LdbPdCov\> | Eval/McsatVsidsPLdbpd

**QE Variants:** The following strategies can be chosen by setting the `SMTRAT_Settings_QE_CAlC` or `SMTRAT_Settings_QE_NuCAD` option in CMake to compile the quantifier elimination variants based on CAlC and NuCAD respectively from the paper. Additionally, pass the argument `--module.parameter qe-method=coverings` to invoke CAlC and the argument `--module.parameter qe-method=nucad` to invoke NuCAD.

Solver | Parameter | Setting
---|---|---
SMT-RAT | coverings | DefaultSettings
CAlC | coverings | EvalSettings
CAlC\<BcLdBounds,BcLdBoundsCov\> | coverings | EvalPBcldboundsSettings
NuCAD | nucad | EvalSettings
NuCAD\<BcLdBounds\> | nucad | EvalPBcldboundsSettings

### Installing and Running Other Tools

We installed the following tool versions. For detailed usage, we also refer to the respective documentation.

* cvc5 version 1.2.0
* Redlog commit 6658
* Tarski version 1.28
* yices2 version 2.6.4
* yicesQS commit 4661444
* z3 version 4.13.4

We provide [Apptainer](https://apptainer.org/) definitions in the `apptainer` directory for building these tools.

#### z3 Variant

The z3-non-port variant is invoked by the command `z3 tactic.default_tactic=qfnra-nlsat input.smt2`.

### QEPCAD B/Tarski and Redlog/Reduce

The `tools-wrapper` directory of this repository contains wrapper Python scripts for running QEPCAD B and Redlog on benchmarks in SMT-LIB format. Instructions:
* Install [Tarski 1.28](https://www.usna.edu/Users/cs/wcbrown/tarski/) 
* Set `tarski_path` in `tarski_wrapper.py`
* Install [Redlog](https://sourceforge.net/projects/reduce-algebra/files/snapshot_2023-12-18/linux64/)
* `pip3 install pysmt`
* Run `tarski_wrapper.py <input.smt2>` or `tarski_wrapper.py <input.smt2>`. The scripts will return either `sat` or `unsat` on SMT benchmarks; or the number of atoms, disjunctions and conjunctions of the solution formula on QE benchmarks. In case the backend is incomplete, it may return `unknown`; if some benchmark uses unsupported features (e.g. division by a non-constant), the scripts will return an error as well.

### Getting the Benchmarks

* QF_NRA: [SMT-LIB Release 2024 (non-incremental benchmarks), QF_NRA logic](https://zenodo.org/records/11061097/files/QF_NRA.tar.zst?download=1).
  * Download and extract.
* NRA: [SMT-LIB Release 2024 (non-incremental benchmarks), NRA logic](https://zenodo.org/records/11061097/files/NRA.tar.zst?download=1).
  * Download and extract.
* QE: [University of Bath: Real Geometry and Connectedness via Triangular Description: CAD Example Bank](https://researchdata.bath.ac.uk/69/).
  * The `tools-wrapper` folder in this repository contains a Python script which downloads the examples from https://researchdata.bath.ac.uk/69/ and converts them to SMT-LIB.
  * Install [Tarski 1.28](https://www.usna.edu/Users/cs/wcbrown/tarski/) (see above).
  * Set `tarski_path` in `smtlib_from_qepcad.py`.
  * Run `david_wilson_to_smtlib.py`. The resulting benchmarks will be written to `qe-benchmarks`.
  * The final set is also contained in the `qe-benchmarks` folder.
* QE-QF_NRA: To run quantifier elimination on the QF_NRA set, you need to replace `(check-sat)` by `(apply qe)` e.g. using:
  
      find ./ -type f -exec sed -i 's/(check-sat)/(apply\ qe)/g' {} \;
* QE-NRA: Same story as for QE-QF_NRA.


### Benchmarking

We do not provide scripts here for running all experiments, as the way this step heavily depends on the user's system.

You may use the benchmarking tool [benchmax](https://github.com/ths-rwth/benchmax-py).

## Verification of Solution Formulas

The solution formulas of SMT-RAT are verified as follows, using the scripts in the `tools-wrapper` directory:
* Install [Tarski 1.40](https://github.com/chriswestbrown/tarski/tree/2e16a504f97fb6c8736ed9126d3e0b696ebbf683) 
* Set `tarski_path` in `tarski_wrapper.py`
* `pip3 install pysmt`
* Adapt `smtrat-nucad.sh` or `smtrat-calc.sh` to contain the path to the SMT-RAT binary.
* Run `verify_qe_result.py smtrat-nucad.sh ./tarski_wrapper.py ../qe-benchmarks/` or `verify_qe_result.py smtrat-calc.sh ./tarski_wrapper.py ../qe-benchmarks/`. Some instances may not be verified due to a timeout of SMT-RAT or Tarski; you can increase this time limit in the `verify_qe_result.py` script.

## Analyzing the Benchmark Set

The statistics about the benchmarks were generated using two tools:

* The script provided in `tools-wrapper/analyzer.py`, which is called as `./analyzer.py input.smt2`.
* SMT-RAT's internal analyzer. For this, SMT-RAT needs to be configured with the CMake option `CLI_ENABLE_ANALYZER=ON`. By calling `./smtrat-static  --analyze.enabled --stats.print --analyze.cnf input.smt2`, the statistics are generated for `input.smt2`.

## Evaluation

The resource at https://doi.org/10.5281/zenodo.16082057 contains a `results` folder with `csv` files containing the results for each solver and benchmark, as well as a folder `evaluation` with Jupyter notebooks to reproduce the figures and tables from the paper. To run the Jupyter notebooks, you need to install a small [python package](https://github.com/ths-rwth/benchmax-py?tab=readme-ov-file#analyzing-the-results). As these script use `tikzplotlib`, you need to use Python 3.9 (or remove tikzplotlib from the notebooks).

    pip3 install pandas matplotlib numpy pillow

    cd ~/.local/lib/python3.9/site-packages/ # path to your python site-packages directory
    ln -s ~/src/smtrat/utilities/benchmax/ # path to the benchmax utility


## Documentation and Contact

For more information, please check out the docs.

* [SMT-RAT documentation](http://ths-rwth.github.io/smtrat)
* [CArL documentation](http://ths-rwth.github.io/carl) (SMT-RAT depends on [CArL](https://github.com/ths-rwth/carl) for formula and polynomial data structures and basic operations)
* Contact *Jasper Nalbach <nalbach@cs.rwth-aachen.de>* in case of questions.