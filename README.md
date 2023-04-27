# SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox

## Exploiting Strict Constraints in the Cylindrical Algebraic Covering

**Contact**

    Jasper Nalbach [nalbach@cs.rwth-aachen.de](mailto:nalbach@cs.rwth-aachen.de)
    Philipp Bär [philipp.baer@rwth-aachen.de](mailto:philipp.baer@rwth-aachen.de)

## Instructions

### Install CArL

Install the CArL version from [RWTH GitLab](https://github.com/ths-rwth/carl/tree/pub/onecell). Starting e.g. in your home directory, use the following commands:

    sudo apt install bison flex
    git clone https://github.com/ths-rwth/carl.git
    cd carl
    git checkout tags/22.04
    mkdir build
    cd build
    cmake ..
    make -j

For further instructions, see the [CArL documentation](http://smtrat.github.io/carl).

### Install SMT-RAT

Return to your initial location to install SMT-RAT, e.g. your home directory. The solver is built using the following commands:

    git clone https://github.com/ths-rwth/smtrat.git -b pub/strict-covering
    cd smtrat
    mkdir build
    cd build
    cmake -DSMTRAT_DEVOPTION_Statistics=ON -DSMTRAT_Strategy=NewCovering ..
    make -j smtrat-static


For further instructions, see the [SMT-RAT documentation](http://smtrat.github.io/).

### Benchmarks

Get the [QF_NRA benchmarks from SMT-LIB](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_NRA/-/tree/r2021-05-26?ref_type=tags). The referenced version was used to evaluate the `NewCovering` Module.

### Running SMT-RAT on a Single Instance

The following command will run SMT-RAT on `input.smt2` and print out statistics for the run:

    ./smtrat-static input.smt2 --stats.print

### Running SMT-RAT on the Whole Benchmark Set

We use benchmax to run the whole QF_NRA dataset. Starting in your initial directory, build benchmax using 

    cd smtrat
    cd build
    make benchmax

and run benchmax on all benchmarks in `/path/to/QF_NRA`. We used a timeout of `1m` and memory limit of `4Gi`. The results (answers, running time, statistics) are written to `out.xml`:

    ./benchmax --statistics -T 1m -M 4Gi -S ./smtrat-static -D /path/to/QF_NRA -X out.xml -b local --use-tmp

Further instructions on running benchmax (i.e. running parallel jobs or using job management systems) can be found in the [documentation](https://smtrat.github.io/dd/d0f/benchmax.html).

## Results

We converted the resulting XML file to CSV using `smtrat/utilities/xml2csv.py`. The CSV files used in the paper are contained in `results/`.
- `CAlC_no_stats.csv`: The results of the original CAlC method on QF_NRA without statistics.
- `CAlC_with_stats.csv`: The results of the original CAlC method on QF_NRA with statistics.
- `CAlC-I_with_new_heuristic_no_stats.csv`: The results of the CAlC-I method with the new heuristic on QF_NRA without statistics.
- `CAlC-I_with_new_heuristic_with_stats.csv`: The results of the CAlC-I method with the new heuristic on QF_NRA with statistics.
- `CAlC-I_without_new_heuristic_with_stats.csv`: The results of the CAlC-I method without the new heuristic on QF_NRA with statistics.

## Statistics

Of particular interest are the following fields:
- `answer`: The result of the solver.
- `runtime`: The runtime of the solver.
- `partial_total_samples`: The number of (partial) sample points used by the solver.
- `partial_ran_samples`: The number of (partial) sample points used by the solver that contain at least one non-rational component.
- `heuristic_called`: Number of intervals created by the solver. Format: `Maximal parent constraint depth,Interval depth+1,Number of intervals`.
- `theorem_holds`: Number of intervals created by the solver by applying the theorem. Format: `Maximal parent constraint depth,Interval depth+1,Number of intervals`.

## Documentation

For more information, please check out the docs.

* [SMT-RAT documentation](http://smtrat.github.io/)
* [CArL documentation](http://smtrat.github.io/carl) (SMT-RAT depends on [CArL](https://github.com/smtrat/carl) for formula and polynomial data structures and basic operations)

