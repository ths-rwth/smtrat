# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#                                                             #
# File: CMakeLists.txt                                        #
#                                                             #
# Project name: SMT-RAT                                       #
# Contact: Florian Corzilius <corzilius@cs.rwth-aachen.de>,   #
#          Ulrich Loup <loup@cs.rwth-aachen.de>               #
# Project sourceforge page: http://smtrat.sourceforge.net/    #
# Development status: beta                                    #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# Version: 2013-04-25                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #


# # # # # # # # # # # # # # # # # # # # # #
# A. Project properties.
# B. Options.
# C. Find system tools and libraries.
# D. Write information files.
# E. Invoke subdirectories.
# F. CPack
# # # # # # # # # # # # # # # # # # # # # #


cmake_minimum_required (VERSION 2.8)

# # # # # # # # # # # # # # # # # # # # # #
# A. Project properties
# # # # # # # # # # # # # # # # # # # # # #
project(smtrat CXX)

set(PROJECT_FULLNAME "SMT-RAT")
set(PROJECT_DESCRIPTION "Satisfiability-Modulo-Theories Real Algebra Toolbox")
set(smtrat_MAJORVERSION 0)
set(smtrat_MINORVERSION 4)
set(smtrat_MAINTENANCEVERSION 0)
set(smtrat_VERSION "${smtrat_MAJORVERSION}.${smtrat_MINORVERSION}.${smtrat_MAINTENANCEVERSION}")
set(PROJECT_VERSION "${smtrat_MAJORVERSION}.${smtrat_MINORVERSION}.${smtrat_MAINTENANCEVERSION}")
set(smtrat_NAME "SMT-RAT" )
set(smtrat_DESCRIPTION ${PROJECT_DESCRIPTION} )


# # # # # # # # # # # # # # # # # # # # # #
# B. Options
# # # # # # # # # # # # # # # # # # # # # #

# options
option( DEVELOPER "Compile with extra warnings" ON )
option(STATICLIB_SWITCH "Compile a statically linked version of the library." OFF)
option(BUILD_SOLVER "Build the SMT-RAT Solver" ON)
option(BUILD_GUI "Build the GUI" OFF)
option(USE_GINAC "If disabled, all implementations using the ginac library are disabled." OFF)

# Strategy
option( SMTRAT_STRAT_Factorization "Factorization" ON )
set(SMTRAT_Strategy "NRATSolver" CACHE STRING "Used strategy in the solver")
option( SMTRAT_STRAT_PARALLEL_MODE "Parallel mode" OFF )

# Development options
option(SMTRAT_DEVOPTION_Validation "Output intermediate states in an smt2 file" ON)
option(SMTRAT_DEVOPTION_MeasureTime "Measure times and number of calls" ON)
option(SMTRAT_DEVOPTION_Statistics "Use the Statistics gathering" ON)

# path to find own modules
set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
# Include own macros.
include( smtratmacros )
# TODO: iteratively search for cmake files and include them here.

if ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "Clang")
    if (APPLE)
        message("-- Using clang on apple")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11 -stdlib=libc++")
    else()
        message("-- Using clang")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")
    endif()
elseif ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
    message("-- Using g++")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++0x")
else()
    message("-- Possibly unsupported compiler")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++0x")
endif()
if(DEVELOPER)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Wconversion")
    set(CMAKE_BUILD_TYPE "DEBUG")
endif()

if("${STATICLIB_SWITCH}" STREQUAL "ON")
	message("-- linking static")
	set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static")
	set(CMAKE_FIND_LIBRARY_SUFFIXES ".a;.so")
endif()

if(${SMTRAT_STRAT_PARALLEL_MODE} STREQUAL "ON")
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,--whole-archive -lpthread -Wl,--no-whole-archive")
endif()

# path to put in the executables
set(EXECUTABLE_OUTPUT_PATH ${PROJECT_BINARY_DIR})

# # # # # # # # # # # # # # # # # # # # # #
# C. Find system tools and libraries.
#
# 1. Required libraries for core.
# 2. Optional libraries for core.
# 3. Required libraries for solver.
# 4. Required libraries for GUI.
# 5. Development and debug libraries.
# # # # # # # # # # # # # # # # # # # # # #

# # # # # # # # # # # # # # # # # # # # # #
# C.1. Required libraries for core.
# # # # # # # # # # # # # # # # # # # # # #

if(${SMTRAT_STRAT_PARALLEL_MODE} STREQUAL "ON")
  set( libraries pthread )
endif()

# GiNaC and GiNaCRA are necessary
# TODO: add support for version number
find_package( carl )
set( libraries ${libraries} )

#notice that GiNacra might use log4cplus, but we cannot currently support that as Ginacra does not export this knowledge.
include( FindCLN REQUIRED )
set( libraries ${libraries} ${CLN_LIBRARY} )

# find gmp (which is necessary for CLN, at least when linking statically)
include( FindGMP REQUIRED )
set( libraries ${libraries} ${GMP_LIBRARY} )

# find itpp (numeric library, used for eigenvalues in rootfinding within ginacra)
include( FindITPP REQUIRED )
if( ${ITPP_FOUND} )
	find_package( LAPACK REQUIRED )
	set( libraries ${libraries} ${ITPP_LIBRARY} ${LAPACK_LIBRARIES} /usr/lib64/gcc/x86_64-pc-linux-gnu/4.7.3/libgfortran.a )
endif()

# # # # # # # # # # # # # # # # # # # # # #
# C.2. required libraries
# # # # # # # # # # # # # # # # # # # # # #

find_package(ReallyNull)
if(ReallyNull_FOUND)
	set(USE_NSS 1)
	set(libraries ${libraries} ${ReallyNull_LIBRARY})
else()
	set(USE_NSS 0)
endif()

# # # # # # # # # # # # # # # # # # # # # #
# C.3. Required libaries for solver.
# # # # # # # # # # # # # # # # # # # # # #

if( BUILD_SOLVER )
	# for building the parser
    find_package(BISON REQUIRED)
    find_package(FLEX REQUIRED)
endif()

# # # # # # # # # # # # # # # # # # # # # #
# C.4. Required libraries for GUI.
# # # # # # # # # # # # # # # # # # # # # #

if( BUILD_GUI )
    find_package(Ant REQUIRED) # for building the GUI
    find_package(Java 1.7 REQUIRED) # for building the GUI
    find_package(Java COMPONENTS Development REQUIRED) # for building the GUI
endif()

# # # # # # # # # # # # # # # # # # # # # #
# C.5. Development and debug libraries.
# # # # # # # # # # # # # # # # # # # # # #

find_package(CPPUnit)

# if doxygen is installed, create the make doc target
include(FindDoxygen)
if(DOXYGEN)
  add_subdirectory(doxygen-conf)
else()
  message(WARNING, "Doxygen not found")
endif()
# add_subdirectory(examples EXCLUDE_FROM_ALL) # offer as an optional target
add_subdirectory(manual EXCLUDE_FROM_ALL)


# # # # # # # # # # # # # # # # # # # # # #
# D. Writen information files
# # # # # # # # # # # # # # # # # # # # # #

# Getting git info.
include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)

configure_file( ${CMAKE_SOURCE_DIR}/smtrat.pc.in ${CMAKE_BINARY_DIR}/smtrat.pc )
# [un]install targets


# specify pkg-config file to be installed
install( FILES ${CMAKE_BINARY_DIR}/smtrat.pc DESTINATION lib/pkgconfig )

# # # # # # # # # # # # # # # # # # # # # #
# E. Invoke subdirectories.
# # # # # # # # # # # # # # # # # # # # # #

add_subdirectory(src)

# # # # # # # # # # # # # # # # # # # # # #
# F. CPack
# # # # # # # # # # # # # # # # # # # # # #

set( CPACK_GENERATOR "TGZ" )
set( CPACK_PACKAGE_FILE_README "${CMAKE_CURRENT_SOURCE_DIROPTIONAL}/README" )
set( CPACK_PACKAGE_DESCRIPTION_SUMMARY ${PROJECT_DESCRIPTION} )
set( CPACK_RESOURCE_FILE_LICENSE "${CMAKE_CURRENT_SOURCE_DIR}/COPYING" )
set( CPACK_PACKAGE_VERSION_MAJOR ${smtrat_MAJORVERSION})
set( CPACK_PACKAGE_VERSION_MINOR ${smtrat_MINORVERSION})
set( CPACK_PACKAGE_VERSION_PATCH ${smtrat_MAINTENANCEVERSION})

set( CPACK_SOURCE_GENERATOR "TGZ;TBZ2" )
set( CPACK_SOURCE_PACKAGE_FILE_NAME smtrat-${smtrat_VERSION} )
set( CPACK_SOURCE_IGNORE_FILES "/build/;/htdocs/;/nbproject/;/CVS/;/\\\\.svn/;/\\\\.bzr/;/\\\\.hg/;/\\\\.git/;/\\\\.deps/;/\\\\.libs/;\\\\.swp$;\\\\.pc$;\\\\.xjs$;\\\\.sh$;ylwrap;\\\\.prej$;\\\\.bak$;\\\\.backup$;~$" )
set( CPACK_SOURCE_IGNORE_FILES ${CPACK_SOURCE_IGNORE_FILES};logo[0-9]+\\\\.png$) # htdocs
set( CPACK_SOURCE_IGNORE_FILES ${CPACK_SOURCE_IGNORE_FILES};\\\\.log$;\\\\.out$;\\\\.toc$;\\\\.aux$;\\\\.pdf$;\\\\.bbl$;\\\\.blg$;) # manual
set( CPACK_SOURCE_IGNORE_FILES ${CPACK_SOURCE_IGNORE_FILES};opensmt-1\\\\.0.1_smtrat-0\\\\.1\\\\.1;) # opensmt binary
#message("CPACK_SOURCE_IGNORE_FILES = ${CPACK_SOURCE_IGNORE_FILES}")
include(CPack)
