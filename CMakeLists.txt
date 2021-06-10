cmake_minimum_required (VERSION 3.7 FATAL_ERROR)

project(smtrat CXX)

# path to find own modules
set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)

# Include own macros.
include(macros)

set_version(21 05)

set(PROJECT_FULLNAME "SMT-RAT")
set(PROJECT_DESCRIPTION "Toolbox for Strategic and Parallel Satisfiability-Modulo-Theories Solving")
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
option( USE_COTIRE "Use cotire to generate and use precompiled headers" OFF )
option( BUILD_SOLVER "Build the SMT-RAT Solver" ON )
option( FORCE_SHIPPED_RESOURCES "Do not look in system for resources which are included" OFF )
option( USE_GINAC "If disabled, all implementations using the ginac library are disabled." OFF )
option( USE_COCOA "Use CoCoALib" ON )
option( ENABLE_TESTING "Enables test target" OFF)

# Strategy
option( SMTRAT_STRAT_Factorization "Factorization" ON )
set(SMTRAT_Strategy "SMTCOMP" CACHE STRING "Used strategy in the solver")
option( SMTRAT_STRAT_PARALLEL_MODE "Parallel mode" OFF )

# Development options
option(SMTRAT_DEVOPTION_Validation "Output intermediate states in an smt2 file" OFF)
option(SMTRAT_DEVOPTION_Statistics "Use the Statistics gathering" OFF)
option(SMTRAT_DEVOPTION_Statistics_Expensive "Enable expensive statistics" OFF)

set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS "DEBUG" "RELEASE" "RELWITHDEBINFO")
set(CLANG_SANITIZER "none" CACHE STRING "Compile with the respective sanitizer")
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

if (NOT CMAKE_BUILD_TYPE)
	set(CMAKE_BUILD_TYPE "RELEASE")
endif()

set(SMTRAT_MANUAL_PATH ${PROJECT_SOURCE_DIR}/doc/manual_${PROJECT_NAME}-${PROJECT_VERSION}.pdf)
set(SMTRAT_MODULES_PATH ${PROJECT_SOURCE_DIR}/src/lib/modules)
# Include own macros.
include( smtratmacros )
# TODO: iteratively search for cmake files and include them here.

include( clang-tidy )
include( clang-time-trace )

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

if(ENABLE_TESTING)
    message("-- testing enabled")
    enable_testing()
endif()

include(compiler-options)

set(DYNAMIC_EXT ".so")
set(STATIC_EXT ".a")
if(APPLE)
	set(DYNAMIC_EXT ".dylib")
	set(STATIC_EXT ".a")
elseif (WIN32)
	set(DYNAMIC_EXT ".dll")
	set(STATIC_EXT ".lib")
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
# C.1. Required libraries for core.
# # # # # # # # # # # # # # # # # # # # # #

include(resources/resources.cmake)

# use carl, carl pulls in the required libraries.

if(STATICLIB_SWITCH)
	set( libraries ${libraries} carl-static)
	set( libraries ${libraries} Boost_STATIC)
else()
	set( libraries ${libraries} carl-shared)
	set( libraries ${libraries} Boost_SHARED)
endif()


# # # # # # # # # # # # # # # # # # # # # #
# C.2. required libraries
# # # # # # # # # # # # # # # # # # # # # #

# # # # # # # # # # # # # # # # # # # # # #
# C.5. Development and debug libraries.
# # # # # # # # # # # # # # # # # # # # # #

if (TARGET Doxygen::doxygen)
	add_subdirectory(doc EXCLUDE_FROM_ALL)
endif()

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

include(export)
include(install)

#include(CMakePackageConfigHelpers)
## Create the carlConfig.cmake and carlConfigVersion files
#file(RELATIVE_PATH REL_INCLUDE_DIR "${CMAKE_INSTALL_DIR}" "${INCLUDE_INSTALL_DIR}")
#message("${CMAKE_INSTALL_DIR}")
#message("${INCLUDE_INSTALL_DIR}")
## ... for the build tree
#set(CONF_INCLUDE_DIRS "${PROJECT_SOURCE_DIR}/src")
#configure_package_config_file(cmake/smtratConfig.cmake.in ${CMAKE_CURRENT_BINARY_DIR}/smtratConfig.cmake
#							  INSTALL_DESTINATION ${CMAKE_INSTALL_DIR}
#							  PATH_VARS INCLUDE_INSTALL_DIR #SYSCONFIG_INSTALL_DIR
#							 )
## ... for the install tree
#set(CONF_INCLUDE_DIRS "\${smtrat_CMAKE_DIR}/${REL_INCLUDE_DIR}")
#configure_package_config_file(cmake/smtratConfig.cmake.in ${CMAKE_CURRENT_BINARY_DIR}${CMAKE_FILES_DIRECTORY}/smtratConfig.cmake
#							  INSTALL_DESTINATION ${CMAKE_INSTALL_DIR}
#							  PATH_VARS INCLUDE_INSTALL_DIR #SYSCONFIG_INSTALL_DIR
#							 )
#write_basic_package_version_file(${CMAKE_CURRENT_BINARY_DIR}/smtratConfigVersion.cmake
#								 VERSION ${smtrat_VERSION}
#								 COMPATIBILITY SameMajorVersion )
#install(FILES ${CMAKE_CURRENT_BINARY_DIR}${CMAKE_FILES_DIRECTORY}/smtratConfig.cmake ${CMAKE_CURRENT_BINARY_DIR}/smtratConfigVersion.cmake
#		DESTINATION ${CMAKE_INSTALL_DIR} )

# Install the export set for use with the install-tree
#message(STATUS "Exporting smtratTargets to ${CMAKE_INSTALL_DIR}")
#install(EXPORT smtratTargets DESTINATION ${CMAKE_INSTALL_DIR} COMPONENT dev)


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

include(prepare-ci)
include(dependency-graph)

add_custom_target(profiling-data)
add_custom_command(
       TARGET profiling-data
       BYPRODUCTS profiling.pdf
       COMMAND gprof -m 0 smtrat-shared gmon.out | gprof2dot -n 0.0 -e 0.0 --strip | dot -Tpdf -oprofiling.pdf
       WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/
)
