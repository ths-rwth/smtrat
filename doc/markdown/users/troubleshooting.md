Troubleshooting {#troubleshooting}
=================================



General 
-----------------------


Mac OS
-----------------------
To be able to build and configure GTest under Mac OSX with clang and libc++ we adjust the CONFIGURE command for gtest in the file resources/CMakeLists.txt to:
~~~~~~
CONFIGURE_COMMAND <SOURCE_DIR>/configure --prefix=<INSTALL_DIR> CXX=/usr/bin/clang++ "CXXFLAGS=-stdlib=libc++ -std=c++11 -DGTEST_USE_OWN_TR1_TUPLE=1"
~~~~~~
