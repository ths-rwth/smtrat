# Installation {#installation}

## Requirements

SMT-RAT is build and tested on Linux.
While MacOS is a secondary target (and should work on the most recent version), we do not target Windows yet. Please contact us if you are interested in changing that.

To build and use SMT-RAT, you need the following other software:

- `git` to checkout the git repository.
- `g++` or `clang` to compile.
- `cmake` to generate the make files.

Optional dependencies
- `ccmake` to set cmake flags.
- `doxygen` and `doxygen-latex` to build the documentation.

Additionally, SMT-RAT requires a few external libraries, which are installed automatically by CMake if no local version is available:
- `carl` from http://smtrat.github.io/carl/ (automatically built locally if necessary).
- `boost` (the boost version from CArL is used).

When installing the dependencies, make sure that you meet the following version requirements:
- `g++` \f$>=\f$ 11
- `clang` \f$>=\f$ 13

## Download

Here are archived versions of SMT-RAT for download:
- [latest](https://github.com/ths-rwth/smtrat/releases)

## Configuration

SMT-RAT is configured with cmake. To prepare the build and perform the configuration run the following, starting from the root folder of SMT-RAT:

	$ mkdir build && cd build && cmake ..
	$ ccmake ..

`ccmake` will show the cmake variables.
[TODO: document important cmake variables]

## Build

To build SMT-RAT use `make` in the build folder:

	$ make smtrat-shared

Relevant targets you may want to build individually include:

- `smtrat-shared`: Builds the (dynamically linked) executable SMT solver
- `smtrat-static`: Builds the (statically linked) executable SMT solver
- `smtrat`: Builds both `smtrat-shared` and `smtrat-static`.
- `doc-html`: Builds the doxygen documentation as HTML.
- `doc-pdf`: Builds the doxygen documentation as PDF.
- `doc`: Builds both `doc-html` and `doc-pdf`.
- `benchmax`: Builds the benchmarking tool.

## Check build

You can now find an executable `smtrat-shared` in the build directory.
It shows some usage information if you run `./smtrat-shared --help`.
To run it on an SMT-LIB file, simply run

	$ ./smtrat-shared example.smt2
