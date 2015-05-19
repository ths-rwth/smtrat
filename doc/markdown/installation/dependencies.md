Dependencies {#dependencies}
==========

To build and use SMT-RAT, you need the following other software:

- `git` to checkout the git repository.
- `g++` or `clang` to compile.
- `boost` for several additional libraries.
- `cmake` to generate the make files.
- `gmp` for calculations with large numbers.
- `carl` from http://smtrat.github.io/carl/

Optional dependencies
- `ccmake` to set cmake flags.
- `doxygen` to build the documentation.
- `ginac` to enable the usage of polynomial factorization.

When installing the dependencies, make sure that you meet the following version requirements:
- `g++` >= 4.8
- `clang` >= 3.4
