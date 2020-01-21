Installation 213 {#installation}
=======

Download
--------
Here are archived versions of SMT-RAT for download:
- [latest](https://github.com/smtrat/smtrat/releases)

We mirror our master branch to github.com. If you want to use the newest bleeding edge version, you can checkout from https://github.com/smtrat/smtrat.
Although we try to keep the master branch stable, there is a chance that the current revision is broken.
You can check [here](https://travis-ci.org/smtrat/smtrat/builds) if the current revision compiles.

Quick installation guide
--------------------------------------------
- Make sure all @subpage dependencies "dependencies" are available.
- Download the latest release or clone the git repository from https://github.com/smtrat/smtrat.git
- Prepare the build.
@code{.sh}
$ mkdir build && cd build && cmake ..
@endcode
- Build SMT-RAT (with tests and documentation).
@code{.sh}
$ make
@endcode
 
Supported platforms
--------------------------------------------
We have tested carl successfully on the following platforms:

- @if Gereon @endif     Arch Linux (Kernel 3.19.2) with Clang 3.6.0 and GCC 4.9.2
- @if Florian @endif    Ubuntu 12.04 LTS with GCC 4.8.1
- @if Florian @endif    MacOSX 10.9 with Clang 3.3
- @if Stefan @endif		MacOSX 10.9.1 with Clang 3.3

Advanced building topics
--------------------------------------------
- @subpage build_cmake
