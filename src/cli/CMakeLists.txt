# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#                                                             #
# File: src/cli/CMakeLists.txt                                #
#                                                             #
# Project name: SMT-RAT                                       #
# Contact: Florian Corzilius <corzilius@cs.rwth-aachen.de>,   #
#          Ulrich Loup <loup@cs.rwth-aachen.de>               #
# Project page: https://github.com/smtrat/smtrat/wiki         #
# Development status: beta                                    #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# Version: 2012-10-10                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

option(CLI_ENABLE_DIMACS_PARSER "Enable parser for DIMACS files" OFF)
option(CLI_ENABLE_FORMULAPARSER "Enable stand-alone formula parser" OFF)
option(CLI_ENABLE_OPB_PARSER "Enable parser for OPB files" OFF)
option(CLI_ENABLE_PREPROCESSOR "Enable stand-alone preprocessor" ON)
option(CLI_ENABLE_QE "Enable quantifier elimination" OFF)


#TODO: are all these directories really necessary?
include_directories(${CMAKE_SOURCE_DIR}/src
                    ${CMAKE_SOURCE_DIR}/src/cli
                    ${CMAKE_BINARY_DIR}/src/cli
 )

#TODO: we only link against the library, which is copied to the binary root dir. We should somehow save that in a variable.
link_directories( ${PROJECT_BINARY_DIR}/src/lib
                  ${PROJECT_BINARY_DIR} )

file(STRINGS ${CMAKE_SOURCE_DIR}/LICENSE LICENSE_CONTENT_IN)

file(GLOB_RECURSE smtrat_cli_tpl "*.in")
foreach(tpl ${smtrat_cli_tpl})
	string(REGEX REPLACE ".in$" "" file ${tpl})
	configure_file("${tpl}" "${file}")
endforeach()

file(GLOB_RECURSE smtrat_cli_sources "*.cpp")

add_library(smtrat-objects OBJECT ${smtrat_cli_sources})
add_dependencies(smtrat-objects
	smtrat-lib-shared
	carl-shared
	smtrat-common-shared
	smtrat-modules-shared
	smtrat-solver-shared
	smtrat-unsat-cores-shared
	smtrat-strategy-${SMTRAT_Strategy}-shared
)
target_include_dirs_from(smtrat-objects "" PUBLIC
	smtrat-lib-shared
	carl-shared
	smtrat-common-shared
	smtrat-modules-shared
	smtrat-solver-shared
	smtrat-unsat-cores-shared
	smtrat-strategy-${SMTRAT_Strategy}-shared
)

add_executable(smtrat-shared $<TARGET_OBJECTS:smtrat-objects>)
add_executable(smtrat-static $<TARGET_OBJECTS:smtrat-objects>)

target_link_libraries(smtrat-shared
	smtrat-lib-shared
	carl-shared
	smtrat-common-shared
	smtrat-modules-shared
	smtrat-solver-shared
	smtrat-unsat-cores-shared
	smtrat-strategy-${SMTRAT_Strategy}-shared
)
target_link_libraries(smtrat-static
	smtrat-lib-static
	carl-static
	smtrat-common-static
	smtrat-modules-static
	smtrat-solver-static
	smtrat-unsat-cores-static
	smtrat-strategy-${SMTRAT_Strategy}-static
)

if(CLI_ENABLE_PREPROCESSOR)
	target_link_libraries(smtrat-shared smtrat-module-FPPModule-shared)
	target_link_libraries(smtrat-static smtrat-module-FPPModule-static)
endif()
if(CLI_ENABLE_QE)
	target_link_libraries(smtrat-shared smtrat-qe-shared)
	target_link_libraries(smtrat-static smtrat-qe-static)
endif()

#if(USE_COTIRE)
#    cotire( smtrat )
#endif()

set_target_properties(smtrat-shared PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})
set_target_properties(smtrat-static PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})

#add_library( smtlibParser
#	${CMAKE_SOURCE_DIR}/src/cli/smtratSolver.cpp
#)

## add linking libraries. This is an over-approximation.
#target_link_libraries( smtlibParser ${libraries})
#
#set_target_properties( smtlibParser PROPERTIES
#		# create *nix style library versions + symbolic links
#		VERSION "${${PROJECT_NAME}_MAJORVERSION}.${${PROJECT_NAME}_MINORVERSION}.${${PROJECT_NAME}_MAINTENANCEVERSION}"
#		SOVERSION "${${PROJECT_NAME}_MAJORVERSION}.${${PROJECT_NAME}_MINORVERSION}.${${PROJECT_NAME}_MAINTENANCEVERSION}"
#		# allow creating static and shared libs without conflicts
#		# CLEAN_DIRECT_OUTPUT 1
#		# avoid conflicts between library and binary target names
#)
#
#if(USE_COTIRE)
#    cotire( smtlibParser )
#endif()
