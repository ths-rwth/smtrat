Dependencies {#dependencies}
==========

To build and use SMT-RAT, you need the following other software:

- `git` to checkout the git repository.
- `cmake` to generate the make files.
- `cln` and `gmp` for calculations with large numbers.
- `Eigen3` for numerical computations.
- `g++` or `clang` to compile.
- `boost` for several additional libraries.
- `carl` from https://ths.informatik.rwth-aachen.de/doxygen/carl/html/

Optional dependencies
- `ccmake` to set cmake flags.
- `doxygen` to build the documentation.
- `gtest` to build the test cases.

To simplify the installation process, `gtest` and `Eigen3` are shipped with CArL in the `resources` folder.
You can build them with
@code
make resources
@endcode

When installing the dependencies, make sure that you meet the following version requirements:
- `g++` >= 4.8
- `clang` >= 3.4
