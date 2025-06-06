cmake_minimum_required (VERSION 3.7 FATAL_ERROR)

#set(CMAKE_DISABLE_SOURCE_CHANGES ON)
set(CMAKE_DISABLE_IN_SOURCE_BUILD ON)

project(smtrat CXX)

if("${PROJECT_SOURCE_DIR}" STREQUAL "${PROJECT_BINARY_DIR}")
   message(SEND_ERROR "In-source builds are not allowed.")
endif()

set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
include(macros)
include(smtratmacros)

set(PROJECT_FULLNAME "SMT-RAT")
set(PROJECT_DESCRIPTION "Toolbox for Strategic and Parallel Satisfiability-Modulo-Theories Solving")
set_version(25 06)

# set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/bin")
set(EXECUTABLE_OUTPUT_PATH ${PROJECT_BINARY_DIR} CACHE PATH "Directory for built executables")
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# # # # # # # # # # # # # # # # # # # # # #
# B. Options
# # # # # # # # # # # # # # # # # # # # # #

# options
option( DEVELOPER "Compile with extra warnings" OFF )
option( LOGGING "Enable logging within the carl library" OFF )
option( BUILD_SOLVER "Build the SMT-RAT Solver" ON )
option( FORCE_SHIPPED_RESOURCES "Do not look in system for resources which are included" OFF )
option( USE_MIMALLOC "Build mimalloc" OFF )

# Strategy
set(SMTRAT_Strategy "Default" CACHE STRING "Used strategy in the solver")
set(SMTRAT_Settings_QE_CAlC "DefaultSettings" CACHE STRING "Settings for CAlC for quantifier elimination")
set(SMTRAT_Settings_QE_NuCAD "DefaultSettings" CACHE STRING "Settings for NuCAD for quantifier elimination")
option( SMTRAT_STRAT_PARALLEL_MODE "Parallel mode" OFF )

# Development options
option(SMTRAT_DEVOPTION_Validation "Output intermediate states in an smt2 file" OFF)
option(SMTRAT_DEVOPTION_Statistics "Use the Statistics gathering" OFF)
option(SMTRAT_DEVOPTION_Checkpoints "Enable checkpoints" OFF)
option(SMTRAT_DEVOPTION_Expensive "Enable expensive logging and assertions" OFF )


set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS "DEBUG" "RELEASE" "RELWITHDEBINFO")
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

if (NOT CMAKE_BUILD_TYPE)
	set(CMAKE_BUILD_TYPE "RELEASE")
endif()

set(SMTRAT_MANUAL_PATH ${PROJECT_SOURCE_DIR}/doc/manual_${PROJECT_NAME}-${PROJECT_VERSION}.pdf)
set(SMTRAT_MODULES_PATH ${PROJECT_SOURCE_DIR}/src/lib/modules)

include( clang-tidy )
include( clang-time-trace )

enable_testing()

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

# # # # # # # # # # # # # # # # # # # # # #
# D. Writen information files
# # # # # # # # # # # # # # # # # # # # # #

configure_file( ${CMAKE_SOURCE_DIR}/smtrat.pc.in ${CMAKE_BINARY_DIR}/smtrat.pc )
# [un]install targets


# specify pkg-config file to be installed
install( FILES ${CMAKE_BINARY_DIR}/smtrat.pc DESTINATION lib/pkgconfig )


# # # # # # # # # # # # # # # # # # # # # #
# F. Invoke subdirectories.
# # # # # # # # # # # # # # # # # # # # # #
add_subdirectory(doc EXCLUDE_FROM_ALL)
add_subdirectory(src)

# # # # # # # # # # # # # # # # # # # # # #
# G. Export Compile Information
# # # # # # # # # # # # # # # # # # # # # #

include(export)
include(install)

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