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
set(ADDITIONAL_INCLUDE_DIRS "" CACHE STRING "Additional directories added to the include directories.")
set(ADDITIONAL_LINK_DIRS "" CACHE STRING "Additional directories added to the link directories.")


# # # # # # # # # # # # # # # # # # # # # #
# B. Options
# # # # # # # # # # # # # # # # # # # # # #

# options
option( DEVELOPER "Compile with extra warnings" ON )
option( STATICLIB_SWITCH "Compile a statically linked version of the library." OFF )
option( LOGGING "Enable logging within the carl library" ON )
option( LOGGING_CARL "Compile with the logging facility of the carl library" ON )
option( BUILD_SOLVER "Build the SMT-RAT Solver" ON )
option( BUILD_GUI "Build the GUI" OFF )
option( USE_GINAC "If disabled, all implementations using the ginac library are disabled." OFF )

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
	set(CMAKE_CXX_RELEASE_FLAGS "${CMAKE_CXX_RELEASE_FLAGS} -O3")
	set(CMAKE_CXX_DEBUG_FLAGS "${CMAKE_CXX_DEBUG_FLAGS} -O1")
elseif ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
    message("-- Using g++")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++0x")
	set(CMAKE_CXX_RELEASE_FLAGS "${CMAKE_CXX_RELEASE_FLAGS} -O3")
	set(CMAKE_CXX_DEBUG_FLAGS "${CMAKE_CXX_DEBUG_FLAGS} -O1")
else()
    message("-- Possibly unsupported compiler")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++0x")
endif()
if(DEVELOPER)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Wconversion -Wno-deprecated-declarations")
    set(CMAKE_BUILD_TYPE "DEBUG")
endif()

message("-- CXX Flags: ${CMAKE_CXX_FLAGS}")
message("-- CXX Debug Flags: ${CMAKE_CXX_DEBUG_FLAGS}")
message("-- CXX Release Flags: ${CMAKE_CXX_RELEASE_FLAGS}")

if(STATICLIB_SWITCH)
	message("-- linking static")
	set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static")
	set(CMAKE_FIND_LIBRARY_SUFFIXES ".a;.so")
endif()

if(SMTRAT_STRAT_PARALLEL_MODE)
	set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,--whole-archive -lpthread -Wl,--no-whole-archive")
	set(libraries ${libraries} pthread)
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

# use carl, carl pulls in the required libraries.
find_package( carl REQUIRED )
message("-- Using CArL from ${carl_INCLUDE_DIR}")

if(STATICLIB_SWITCH)
	set( libraries ${libraries} lib_carl_static)
else()
	set( libraries ${libraries} lib_carl)
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
# E. Source file aggregation and clustering
# # # # # # # # # # # # # # # # # # # # # #

file(GLOB_RECURSE SMTRAT_HEADERS ${PROJECT_SOURCE_DIR}/src/*.h)
file(GLOB_RECURSE SMTRAT_SOURCES ${PROJECT_SOURCE_DIR}/src/*/*.cpp)
file(GLOB_RECURSE SMTRAT_MAIN_FILE ${PROJECT_SOURCE_DIR}/src/solver/smtratSolver.cpp)
file(GLOB SMTRAT_SOLVER_FILES ${PROJECT_SOURCE_DIR}/src/solver/*.h ${PROJECT_SOURCE_DIR}/src/solver/*.cpp)
file(GLOB_RECURSE SMTRAT_PARSER_FILES ${PROJECT_SOURCE_DIR}/src/solver/parser/*.h ${PROJECT_SOURCE_DIR}/src/solver/parser/*.cpp)
file(GLOB SMTRAT_LIB_FILES ${PROJECT_SOURCE_DIR}/src/lib/*.h ${PROJECT_SOURCE_DIR}/src/lib/*.cpp)
file(GLOB_RECURSE SMTRAT_UTILITY_FILES ${PROJECT_SOURCE_DIR}/src/lib/utilities/*.h ${PROJECT_SOURCE_DIR}/src/lib/utilities/*.cpp)
file(GLOB_RECURSE SMTRAT_STRATEGY_FILES ${PROJECT_SOURCE_DIR}/src/lib/strategies/*.h ${PROJECT_SOURCE_DIR}/src/lib/strategies/*.cpp)
file(GLOB_RECURSE SMTRAT_MISC_FILES ${PROJECT_SOURCE_DIR}/src/lib/misc/*.h ${PROJECT_SOURCE_DIR}/src/lib/misc/*.cpp)
file(GLOB SMTRAT_DATASTRUCTURE_FILES ${PROJECT_SOURCE_DIR}/src/lib/datastructures/*.h ${PROJECT_SOURCE_DIR}/src/lib/datastructures/*.cpp)
file(GLOB_RECURSE SMTRAT_DATASTRUCTURE_VS_FILES ${PROJECT_SOURCE_DIR}/src/lib/datastructures/vs/*.h ${PROJECT_SOURCE_DIR}/src/lib/datastructures/vs/*.cpp)
file(GLOB_RECURSE SMTRAT_DATASTRUCTURE_LRA_FILES ${PROJECT_SOURCE_DIR}/src/lib/datastructures/lra/*.h ${PROJECT_SOURCE_DIR}/src/lib/datastructures/lra/*.cpp)
file(GLOB SMTRAT_MODULES_FILES ${PROJECT_SOURCE_DIR}/src/lib/modules/*.h ${PROJECT_SOURCE_DIR}/src/lib/modules/*.cpp)
file(GLOB_RECURSE SMTRAT_CACHE_MODULE_FILES ${PROJECT_SOURCE_DIR}/src/lib/modules/CacheModule/*.h ${PROJECT_SOURCE_DIR}/src/lib/modules/CacheModule/*.cpp)
file(GLOB_RECURSE SMTRAT_CAD_MODULE_FILES ${PROJECT_SOURCE_DIR}/src/lib/modules/CADModule/*.h ${PROJECT_SOURCE_DIR}/src/lib/modules/CADModule/*.cpp)
file(GLOB_RECURSE SMTRAT_CNFER_MODULE_FILES ${PROJECT_SOURCE_DIR}/src/lib/modules/CNFerModule/*.h ${PROJECT_SOURCE_DIR}/src/lib/modules/CNFerModule/*.cpp)
file(GLOB_RECURSE SMTRAT_GB_MODULE_FILES ${PROJECT_SOURCE_DIR}/src/lib/modules/GBModule/*.h ${PROJECT_SOURCE_DIR}/src/lib/modules/GBModule/*.cpp)
file(GLOB_RECURSE SMTRAT_ICP_MODULE_FILES ${PROJECT_SOURCE_DIR}/src/lib/modules/ICPModule/*.h ${PROJECT_SOURCE_DIR}/src/lib/modules/ICPModule/*.cpp)
file(GLOB_RECURSE SMTRAT_LRA_MODULE_FILES ${PROJECT_SOURCE_DIR}/src/lib/modules/LRAModule/*.h ${PROJECT_SOURCE_DIR}/src/lib/modules/LRAModule/*.cpp)
file(GLOB_RECURSE SMTRAT_PREPROCESSING_MODULE_FILES ${PROJECT_SOURCE_DIR}/src/lib/modules/PreprocessingModule/*.h ${PROJECT_SOURCE_DIR}/src/lib/modules/PreprocessingModule/*.cpp)
file(GLOB_RECURSE SMTRAT_REDUCE_MODULE_FILES ${PROJECT_SOURCE_DIR}/src/lib/modules/ReduceModule/*.h ${PROJECT_SOURCE_DIR}/src/lib/modules/ReduceModule/*.cpp)
file(GLOB_RECURSE SMTRAT_SAT_MODULE_FILES ${PROJECT_SOURCE_DIR}/src/lib/modules/SATModule/*.h ${PROJECT_SOURCE_DIR}/src/lib/modules/SATModule/*.cpp)
file(GLOB_RECURSE SMTRAT_SINGLEVS_MODULE_FILES ${PROJECT_SOURCE_DIR}/src/lib/modules/SingleVSModule/*.h ${PROJECT_SOURCE_DIR}/src/lib/modules/SingleVSModule/*.cpp)
file(GLOB_RECURSE SMTRAT_SMART_SIMPLIFIER_MODULE_FILES ${PROJECT_SOURCE_DIR}/src/lib/modules/SmartSimplifier/*.h ${PROJECT_SOURCE_DIR}/src/lib/modules/SmartSimplifier/*.cpp)
file(GLOB_RECURSE SMTRAT_VRW_MODULE_FILES ${PROJECT_SOURCE_DIR}/src/lib/modules/VRWModule/*.h ${PROJECT_SOURCE_DIR}/src/lib/modules/VRWModule/*.cpp)
file(GLOB_RECURSE SMTRAT_VS_MODULE_FILES ${PROJECT_SOURCE_DIR}/src/lib/modules/VSModule/*.h ${PROJECT_SOURCE_DIR}/src/lib/modules/VSModule/*.cpp)

# Group the headers and sources
source_group(main FILES ${SMTRAT_MAIN_FILE})
source_group(lib FILES ${SMTRAT_LIB_FILES})
source_group(lib\\misc FILES ${SMTRAT_MISC_FILES})
source_group(lib\\datastructures FILES ${SMTRAT_DATASTRUCTURE_FILES})
source_group(lib\\datastructures\\lra FILES ${SMTRAT_DATASTRUCTURE_LRA_FILES})
source_group(lib\\datastructures\\vs FILES ${SMTRAT_DATASTRUCTURE_VS_FILES})
source_group(lib\\modules FILES ${SMTRAT_MODULES_FILES})
source_group(lib\\modules\\CacheModule FILES ${SMTRAT_CACHE_MODULE_FILES})
source_group(lib\\modules\\CADModule FILES ${SMTRAT_CAD_MODULE_FILES})
source_group(lib\\modules\\CNFerModule FILES ${SMTRAT_CNFER_MODULE_FILES})
source_group(lib\\modules\\GBModule FILES ${SMTRAT_GB_MODULE_FILES})
source_group(lib\\modules\\ICPModule FILES ${SMTRAT_ICP_MODULE_FILES})
source_group(lib\\modules\\LRAModule FILES ${SMTRAT_LRA_MODULE_FILES})
source_group(lib\\modules\\PreprocessingModule FILES ${SMTRAT_PREPROCESSING_MODULE_FILES})
source_group(lib\\modules\\ReduceModule FILES ${SMTRAT_REDUCE_MODULE_FILES})
source_group(lib\\modules\\SATModule FILES ${SMTRAT_SAT_MODULE_FILES})
source_group(lib\\modules\\SingleVSModule FILES ${SMTRAT_SINGLEVS_MODULE_FILES})
source_group(lib\\modules\\SmartSimplifier FILES ${SMTRAT_SMART_MODULE_FILES})
source_group(lib\\modules\\VRWModule FILES ${SMTRAT_VRW_MODULE_FILES})
source_group(lib\\modules\\VSModule FILES ${SMTRAT_VS_MODULE_FILES})

# Add custom additional include or link directories
if (ADDITIONAL_INCLUDE_DIRS)
	message(STATUS "SMT-RAT - Using additional include directories ${ADDITIONAL_INCLUDE_DIRS}")
	include_directories(${ADDITIONAL_INCLUDE_DIRS})
endif(ADDITIONAL_INCLUDE_DIRS)
if (ADDITIONAL_LINK_DIRS)
	message(STATUS "SMT-RAT - Using additional link directories ${ADDITIONAL_LINK_DIRS}")
	link_directories(${ADDITIONAL_LINK_DIRS})
endif(ADDITIONAL_LINK_DIRS)

# # # # # # # # # # # # # # # # # # # # # #
# F. Invoke subdirectories.
# # # # # # # # # # # # # # # # # # # # # #

add_subdirectory(src)

# # # # # # # # # # # # # # # # # # # # # #
# G. CPack
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
