# Installation {#installation}

To install SMT-RAT, follow the steps below.

## Download
Here are archived versions of SMT-RAT for download:
- [latest](https://github.com/smtrat/smtrat/releases)

We mirror our master branch to github.com. If you want to use the newest bleeding edge version, you can checkout from https://github.com/smtrat/smtrat.
Although we try to keep the master branch stable, there is a chance that the current revision is broken.
You can check [here](https://travis-ci.org/smtrat/smtrat/builds) if the current revision compiles.

## Dependencies

To build and use SMT-RAT, you need the following other software:

- `git` to checkout the git repository.
- `g++` or `clang` to compile.
- `cmake` to generate the make files.
- `boost` for several additional libraries (automatically built locally if necessary).
- `gmp` for calculations with large numbers (automatically built locally if necessary).
- `carl` from http://smtrat.github.io/carl/ (automatically built locally if necessary).

Optional dependencies
- `ccmake` to set cmake flags.
- `doxygen` to build the documentation.
- `ginac` to enable the usage of polynomial factorization.

When installing the dependencies, make sure that you meet the following version requirements:
- `g++` \f$>=\f$ 7
- `clang` \f$>=\f$ 5

## Configuration

SMT-RAT is configured with cmake. To prepare the build and perform the configuration run the following:

@code{.sh}
$ mkdir build && cd build && cmake ..
$ ccmake ..
@endcode

`ccmake` will show the cmake variables. Important variables you may want to change include the following:


## Build

To build SMT-RAT (with tests and documentation), simply run

@code{.sh}
$ make
@endcode

Relevant targets you may want to build individually include:

- `doc-html`: Builds the doxygen documentation as HTML.
- `doc-pdf`: Builds the doxygen documentation as PDF.
- `doc`: Builds both `doc-html` and `doc-pdf`.
- `smtrat-shared`: Builds the (dynamically linked) executable SMT solver
- `smtrat-static`: Builds the (dynamically linked) executable SMT solver
- `smtrat`: Builds both `smtrat-shared` and `smtrat-static`.
- `benchmax`: Builds the benchmarking tool.
- `delta`: Builds the delta debugger.

