# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#                                                             #
# File: CMakeLists.txt                                        #
#                                                             #
# Project name: SMT-RAT                                       #
# Contact: Florian Corzilius <corzilius@cs.rwth-aachen.de>,   #
#          Ulrich Loup <loup@cs.rwth-aachen.de>               #
# Project page: https://github.com/smtrat/smtrat/wiki         #
# Development status: beta                                    #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# Version: 2013-04-25                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #


# # # # # # # # # # # # # # # # # # # # # #
# A. Project properties.
# B. Options.
# C. Find system tools and libraries.
# D. Write information files.
# F. Invoke subdirectories.
# G. Export Compile Information
# H. CPack
# # # # # # # # # # # # # # # # # # # # # #

if (WIN32)
	cmake_minimum_required (VERSION 3.1 FATAL_ERROR)
else()
	cmake_minimum_required (VERSION 2.8.12)
endif()

# # # # # # # # # # # # # # # # # # # # # #
# A. Project properties
# # # # # # # # # # # # # # # # # # # # # #
project(smtrat CXX)

set(PROJECT_FULLNAME "SMT-RAT")
set(PROJECT_DESCRIPTION "Toolbox for Strategic and Parallel Satisfiability-Modulo-Theories Solving")
set(smtrat_MAJORVERSION 2)
set(smtrat_MINORVERSION 1)
set(smtrat_MAINTENANCEVERSION 0)
set(smtrat_VERSION "${smtrat_MAJORVERSION}.${smtrat_MINORVERSION}.${smtrat_MAINTENANCEVERSION}")
set(PROJECT_VERSION "${smtrat_MAJORVERSION}.${smtrat_MINORVERSION}.${smtrat_MAINTENANCEVERSION}")
set(smtrat_NAME "SMT-RAT" )
set(smtrat_DESCRIPTION ${PROJECT_DESCRIPTION} )
set(ADDITIONAL_INCLUDE_DIRS "" CACHE STRING "Additional directories added to the include directories.")
set(ADDITIONAL_LINK_DIRS "" CACHE STRING "Additional directories added to the link directories.")

# set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/bin")
set(EXECUTABLE_OUTPUT_PATH ${PROJECT_BINARY_DIR} CACHE PATH "Directory for built executables")
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# # # # # # # # # # # # # # # # # # # # # #
# B. Options
# # # # # # # # # # # # # # # # # # # # # #

# options
option( DEVELOPER "Compile with extra warnings" OFF )
option( STATICLIB_SWITCH "Compile a statically linked version of the library." OFF )
option( LOGGING "Enable logging within the carl library" OFF )
option( LOGGING_CARL "Compile with the logging facility of the carl library" OFF )
option( USE_COTIRE "Use cotire to generate and use precompiled headers" OFF )
option( BUILD_SOLVER "Build the SMT-RAT Solver" ON )
option( BUILD_GUI "Build the GUI" OFF )
option( USE_GINAC "If disabled, all implementations using the ginac library are disabled." OFF )
option(${PROJECT_NAME}_DOC_CREATE_PDF "Create PDF reference manual" ON )

# Strategy
option( SMTRAT_STRAT_Factorization "Factorization" ON )
set(SMTRAT_Strategy "RatComp2016" CACHE STRING "Used strategy in the solver")
option( SMTRAT_STRAT_PARALLEL_MODE "Parallel mode" OFF )

# Development options
option(SMTRAT_DEVOPTION_Validation "Output intermediate states in an smt2 file" OFF)
option(SMTRAT_DEVOPTION_MeasureTime "Measure times and number of calls" OFF)
option(SMTRAT_DEVOPTION_Statistics "Use the Statistics gathering" OFF)

set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS "DEBUG" "RELEASE")

if (NOT CMAKE_BUILD_TYPE)
	set(CMAKE_BUILD_TYPE "RELEASE")
endif()

# path to find own modules
set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)

set(SMTRAT_MANUAL_PATH ${PROJECT_SOURCE_DIR}/manual/manual_${PROJECT_NAME}-${PROJECT_VERSION}.pdf)
set(SMTRAT_MODULES_PATH ${PROJECT_SOURCE_DIR}/src/lib/modules)
# Include own macros.
include( smtratmacros )
# TODO: iteratively search for cmake files and include them here.

if(USE_COTIRE)
	# We use cotire, simply include it
	message("-- using cotire")
	include(cotire)
else()
	# We do not use cotire, create dummy function.
	message("-- not using cotire")
	function(cotire)
	endfunction(cotire)
endif()

if ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "Clang")
    if (APPLE)
        message("-- Using clang on apple")
        set(CMAKE_MACOSX_RPATH 1)
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++14 -stdlib=libc++")
    else()
        message("-- Using clang")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++14")
    endif()
	set(CMAKE_CXX_RELEASE_FLAGS "${CMAKE_CXX_RELEASE_FLAGS} -O3")
	set(CMAKE_CXX_DEBUG_FLAGS "${CMAKE_CXX_DEBUG_FLAGS} -g -O0")
elseif ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
    message("-- Using g++")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++14")
	set(CMAKE_CXX_RELEASE_FLAGS "${CMAKE_CXX_RELEASE_FLAGS} -O3")
	set(CMAKE_CXX_DEBUG_FLAGS "${CMAKE_CXX_DEBUG_FLAGS} -g -O1")
elseif ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
    message("-- Using Visual Studio C++")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /MP")
    set(CMAKE_CXX_RELEASE_FLAGS "${CMAKE_CXX_RELEASE_FLAGS} /O2")
    set(CMAKE_CXX_DEBUG_FLAGS "${CMAKE_CXX_DEBUG_FLAGS} /MTd")
else()
    message("-- Possibly unsupported compiler")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")
endif()
if(DEVELOPER)
	if ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
		set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /Wall")
	else()
		set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Wconversion -Wno-deprecated-declarations")
	endif()
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DDEBUG")
	set(CMAKE_BUILD_TYPE "DEBUG")
endif()

message("-- CXX Flags: ${CMAKE_CXX_FLAGS}")
message("-- CXX Debug Flags: ${CMAKE_CXX_DEBUG_FLAGS}")
message("-- CXX Release Flags: ${CMAKE_CXX_RELEASE_FLAGS}")

if(STATICLIB_SWITCH)
    message("-- linking static")
    if (APPLE)
        set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -mmacosx-version-min=10.7")
    else()
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fPIE")
	set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static")
	set(CMAKE_EXE_LINK_DYNAMIC_C_FLAGS "")
	set(CMAKE_EXE_LINK_DYNAMIC_CXX_FLAGS "")
	set(CMAKE_SHARED_LIBRARY_LINK_C_FLAGS "")
	set(CMAKE_SHARED_LIBRARY_LINK_CXX_FLAGS "")
	set(LINK_SEARCH_START_STATIC "")
	set(LINK_SEARCH_END_STATIC "")
    endif()
    set(CMAKE_FIND_LIBRARY_SUFFIXES ".a;.so")
endif()

if(SMTRAT_STRAT_PARALLEL_MODE)
    if (APPLE)
	set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl -lpthread -Wl")
    else()
	set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,--whole-archive -lpthread -Wl,--no-whole-archive")
    endif()
    set(libraries ${libraries} pthread)
endif()

if(WIN32 AND NOT CYGWIN)
  set(DEF_INSTALL_CMAKE_DIR CMake)
else()
  set(DEF_INSTALL_CMAKE_DIR lib/CMake/smtrat)
endif()
set(CMAKE_INSTALL_DIR ${DEF_INSTALL_CMAKE_DIR} CACHE PATH  "Installation directory for CMake files")


foreach(p LIB BIN INCLUDE CMAKE)
  set(var ${p}_INSTALL_DIR)
  if(NOT IS_ABSOLUTE "${${var}}")
    set(${var} "${CMAKE_INSTALL_PREFIX}/${${var}}")
  endif()
endforeach()


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
message(STATUS "Using CArL from ${carl_INCLUDE_DIR}")

if(STATICLIB_SWITCH)
	set( libraries ${libraries} lib_carl_static)
	set( libraries ${libraries} Boost_STATIC)
else()
	set( libraries ${libraries} lib_carl)
	set( libraries ${libraries} Boost_SHARED)
endif()


# # # # # # # # # # # # # # # # # # # # # #
# C.2. required libraries
# # # # # # # # # # # # # # # # # # # # # #

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
# G. Export Compile Information
# # # # # # # # # # # # # # # # # # # # # #

# Add all targets to the build-tree export set
export(TARGETS ${SMTRAT_TARGETS} FILE "${PROJECT_BINARY_DIR}/smtratTargets.cmake")

# Export the package for use from the build-tree
# (this registers the build-tree with a global CMake-registry)
export(PACKAGE smtrat)

include(CMakePackageConfigHelpers)
# Create the carlConfig.cmake and carlConfigVersion files
file(RELATIVE_PATH REL_INCLUDE_DIR "${CMAKE_INSTALL_DIR}" "${INCLUDE_INSTALL_DIR}")
message("${CMAKE_INSTALL_DIR}")
message("${INCLUDE_INSTALL_DIR}")
# ... for the build tree
set(CONF_INCLUDE_DIRS "${PROJECT_SOURCE_DIR}/src")
configure_package_config_file(cmake/smtratConfig.cmake.in ${CMAKE_CURRENT_BINARY_DIR}/smtratConfig.cmake
							  INSTALL_DESTINATION ${CMAKE_INSTALL_DIR}
							  PATH_VARS INCLUDE_INSTALL_DIR #SYSCONFIG_INSTALL_DIR
							 )
# ... for the install tree
set(CONF_INCLUDE_DIRS "\${smtrat_CMAKE_DIR}/${REL_INCLUDE_DIR}")
configure_package_config_file(cmake/smtratConfig.cmake.in ${CMAKE_CURRENT_BINARY_DIR}${CMAKE_FILES_DIRECTORY}/smtratConfig.cmake
							  INSTALL_DESTINATION ${CMAKE_INSTALL_DIR}
							  PATH_VARS INCLUDE_INSTALL_DIR #SYSCONFIG_INSTALL_DIR
							 )
write_basic_package_version_file(${CMAKE_CURRENT_BINARY_DIR}/smtratConfigVersion.cmake
								 VERSION ${smtrat_VERSION}
								 COMPATIBILITY SameMajorVersion )
install(FILES ${CMAKE_CURRENT_BINARY_DIR}${CMAKE_FILES_DIRECTORY}/smtratConfig.cmake ${CMAKE_CURRENT_BINARY_DIR}/smtratConfigVersion.cmake
		DESTINATION ${CMAKE_INSTALL_DIR} )

# Install the export set for use with the install-tree
install(EXPORT smtratTargets DESTINATION ${CMAKE_INSTALL_DIR} COMPONENT dev)


# # # # # # # # # # # # # # # # # # # # # #
# H. CPack
# # # # # # # # # # # # # # # # # # # # # #

set( CPACK_GENERATOR "TGZ" )
set( CPACK_PACKAGE_FILE_README "${CMAKE_CURRENT_SOURCE_DIROPTIONAL}/README" )
set( CPACK_PACKAGE_DESCRIPTION_SUMMARY ${PROJECT_DESCRIPTION} )
set( CPACK_RESOURCE_FILE_LICENSE "${CMAKE_CURRENT_SOURCE_DIR}/LICENSE" )
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
