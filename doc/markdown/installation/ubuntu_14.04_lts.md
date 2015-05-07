Ubuntu 14.04 LTS 64Bit {#ubuntu_1404_lts}
==========

This is an example how the installation on Ubuntu 14.04 LTS 64Bit looks like.
We assume that you start with a fresh installation and know how to install software packages.

- Install the following packages:
 - `git`
 - `cmake` and `cmake-curses-gui`
 - `libcln6`, `libcln-dev` and `libgmp-dev`
 - `libeigen3-dev`
 - `g++` or `clang`
 - `libboost-dev`
 - `doxygen`

- Checkout CArL:
@code
git clone https://<user>@srv-i2.informatik.rwth-aachen.de:8443/git/carl.git
@endcode

- Create `build` folder:
@code 
cd carl/
mkdir build
cd build/
@endcode

- Run CMake:
@code
cmake ../
@endcode
By default, `c++` will be used as compiler which points to `g++`. This, and many other options, can be configured using `ccmake`.

- Build `libcarl`:
@code
make lib_carl
@endcode
This builds the shared library `build/libcarl.so`.

- Build and run tests:
@code
make googletest
make
make test
@endcode
The individual tests are stored in `build/bin/`.

- Build documentation:
@code
make doc
@endcode
The documentation is stored in `build/doc/`.
