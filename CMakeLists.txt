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
# Version: 2012-06-08                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

# common settings
# # # # # # # # #

cmake_minimum_required (VERSION 2.8)

option(USE_NSS "Compile the NSS Module")
option(USE_GINACRA "Compile modules using GiNaCRA")
option(USE_GB "Compile modules using GroebnerBasis")
option(USE_CAD "Compile modules using CAD")

if(NOT USE_GINACRA) 
	if(USE_GB)
		message(WARNING, "GB is automatically switched off when GiNaCRA is not available")
	endif()
	SET(USE_GB FALSE)
	if(USE_CAD)
		message(WARNING, "CAD is automatically switched off when GiNaCRA is not available")
	endif()
	SET(USE_CAD FALSE)
endif()

if(NOT USE_GB) 
	if(USE_NSS) 
		message(WARNING, "NSS is automatically switched off when Groebner Basis are not used")
	endif()
	SET(USE_NSS FALSE)
endif()

if(USE_NSS)
	project(smtrat CXX Fortran C)
else()
	project(smtrat CXX)
endif()

set(CMAKE_CXX_FLAGS ${CMAKE_CXX_FLAGS} "-Wall -g -std=c++0x")


# information about the project
set( PROJECT_FULLNAME "SMT-RAT")
set( PROJECT_DESCRIPTION "Satisfiability-Modulo-Theories Real Algebra Toolbox")
set( smtrat_MAJORVERSION 0)
set( smtrat_MINORVERSION 2)
set( smtrat_MAINTENANCEVERSION 1)
set( smtrat_VERSION "${smtrat_MAJORVERSION}.${smtrat_MINORVERSION}.${smtrat_MAINTENANCEVERSION}")
set( PROJECT_VERSION "${smtrat_MAJORVERSION}.${smtrat_MINORVERSION}.${smtrat_MAINTENANCEVERSION}")
set( smtrat_NAME "SMT-RAT" )
set( smtrat_DESCRIPTION ${PROJECT_DESCRIPTION} )

# options
option( STATICLIB_SWITCH "Compile a statically linked version of the library." )


# path to find own modules
set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)


# path to put in the executables
set(EXECUTABLE_OUTPUT_PATH ${PROJECT_BINARY_DIR})

# required libraries
# # # # # # # # # # #

# GiNaCRA libraries and tools all need GiNaC
# TODO: add support for version number
find_package(GiNaC REQUIRED)
if(USE_GINACRA)
	find_package(GiNaCRA REQUIRED)
endif()


# find CLN ..
# TODO: we should write a find-module for this
include(FindPkgConfig)
pkg_check_modules(cln REQUIRED cln>=1.2.2)
# On ELF systems (such as GNU/Linux) this prevents the infamous `error
# while loading shared libraries: libfoo.so: cannot open shared object
# file: no such file or directory'
set(CMAKE_INSTALL_RPATH_USE_LINK_RPATH TRUE)
list(FIND CMAKE_PLATFORM_IMPLICIT_LINK_DIRECTORIES "${cln_LIBRARY_DIRS}" isSystemDir)
if("${isSystemDir}" STREQUAL "-1")
	set(CMAKE_INSTALL_RPATH "${CMAKE_INSTALL_RPATH}:${cln_LIBRARY_DIRS}")
endif()

# optional libraries
# # # # # # # # # # #

find_package(CPPUnit)
find_package(Ant) # for building the GUI
find_package(Java) # for building the GUI
find_package(Java COMPONENTS Development) # for building the GUI
find_package(BISON) # for building the parser
find_package(FLEX) # for building the parser

# LAPACK and BLAS are both needed for successfull using CSDP
# todo: maybe CLAPACK would also do?

if(USE_NSS)
	enable_language(Fortran) 
	find_package(LAPACK)
	find_package(BLAS)

	add_custom_target(
		csdp_lib
		COMMAND make
		WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/external/csdp
	)	
endif()

# GUI settings
# # # # # # # #
set( JAR_NAME "SMT-XRAT" )
set( DOLLAR "$" )

# further directories to be included
# # # # # # # # # # # # # # # # # # #
add_subdirectory(src)
add_subdirectory(src/gui EXCLUDE_FROM_ALL)

# if doxygen is installed, create the make doc target
include(FindDoxygen)
if(DOXYGEN)
  add_subdirectory(doxygen-conf)
else()
  message(WARNING, "Doxygen not found")
endif()
# add_subdirectory(examples EXCLUDE_FROM_ALL) # offer as an optional target
add_subdirectory(manual EXCLUDE_FROM_ALL)

# configure file specification in order to translate CMake variables to C++
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

configure_file( ${CMAKE_SOURCE_DIR}/smtrat.pc.in ${CMAKE_BINARY_DIR}/smtrat.pc )
configure_file( ${CMAKE_SOURCE_DIR}/src/config.h.in ${CMAKE_SOURCE_DIR}/src/config.h )

# [un]install targets
# # # # # # # # # # #

# specify pkg-config file to be installed
install( FILES ${CMAKE_BINARY_DIR}/smtrat.pc DESTINATION lib/pkgconfig )

# packaging target (cpack)
# # # # # # # # # # # # # #

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
