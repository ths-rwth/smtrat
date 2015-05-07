Windows 7 64Bit {#windows_7_msvc2014}
==========

This is an example how the installation on Windows 7 64Bit looks like.
We assume that you start with a fresh installation and know how to install software.

Warning: This guide is incomplete!

This guide is for a Visual Studio 2013 (which is Visual Studio 12).

- Install the following software:
 - `git`
 - `cmake`
 - `boost`: Extract the boost sources to `C:\Program Files\boost\`.
 - `cln`: Extract the cln sources to `C:\Program Files\cln\`. You need to extract a `.tar.bz2` archive.

- Run CMake:
 - Open a shell within the CArL folder
 - Create a build folder `build/`
 - Run the following command in the `build/` folder:
@code
cmake -G "Visual Studio 12" ../
@endcode
