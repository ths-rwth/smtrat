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

option(CLI_ENABLE_ANALYZER "Enable stand-alone formula analyzer" OFF)
option(CLI_ENABLE_DIMACS_PARSER "Enable parser for DIMACS files" OFF)
option(CLI_ENABLE_FORMULAPARSER "Enable stand-alone formula parser" OFF)
option(CLI_ENABLE_OPB_PARSER "Enable parser for OPB files" OFF)
option(CLI_ENABLE_PREPROCESSOR "Enable stand-alone preprocessor" ON)
option(CLI_ENABLE_QE "Enable quantifier elimination" OFF)

include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

#TODO: are all these directories really necessary?
include_directories(${CMAKE_SOURCE_DIR}/src
                    ${CMAKE_SOURCE_DIR}/src/cli
                    ${CMAKE_BINARY_DIR}/src/cli
 )

#TODO: we only link against the library, which is copied to the binary root dir. We should somehow save that in a variable.
link_directories( ${PROJECT_BINARY_DIR}/src/lib
                  ${PROJECT_BINARY_DIR} )

file(STRINGS ${CMAKE_SOURCE_DIR}/LICENSE LICENSE_CONTENT_IN)

get_cmake_property(variableNames VARIABLES)
set(VARLIST "")
foreach (variableName ${variableNames})
	get_property(ISADV CACHE ${variableName} PROPERTY ADVANCED SET)
	get_property(TYPE CACHE ${variableName} PROPERTY TYPE)
	set(VARLIST "${VARLIST}\n\tprint(${ISADV}, \"${TYPE}\", \"${variableName}\", R\"VAR(${${variableName}})VAR\");")
endforeach()

configure_everything()

file(GLOB_RECURSE smtrat_cli_sources "*.cpp")

add_library(smtrat-objects OBJECT ${smtrat_cli_sources})
add_dependencies(smtrat-objects
	smtrat-lib-shared
	carl-shared
	carl-io-shared
	smtrat-common-shared
	smtrat-solver-shared
	smtrat-unsat-cores-shared
	smtrat-strategy-${SMTRAT_Strategy}-shared
)
target_include_dirs_from(smtrat-objects "" PUBLIC
	smtrat-lib-shared
	carl-shared
	carl-io-shared
	smtrat-common-shared
	smtrat-solver-shared
	smtrat-unsat-cores-shared
	smtrat-strategy-${SMTRAT_Strategy}-shared
)

add_executable(smtrat-shared $<TARGET_OBJECTS:smtrat-objects>)
add_executable(smtrat-static $<TARGET_OBJECTS:smtrat-objects>)

target_link_libraries(smtrat-shared
	smtrat-lib-shared
	carl-shared
	carl-io-shared
	smtrat-common-shared
	smtrat-solver-shared
	smtrat-unsat-cores-shared
	smtrat-strategy-${SMTRAT_Strategy}-shared
)
target_link_libraries(smtrat-static
	"-static"
	smtrat-lib-static
	carl-static
	carl-io-static
	smtrat-common-static
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
if(CLI_ENABLE_FORMULAPARSER)
	target_link_libraries(smtrat-shared smtrat-analyzer-shared)
	target_link_libraries(smtrat-static smtrat-analyzer-static)
endif()


set_target_properties(smtrat-shared PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})
set_target_properties(smtrat-static PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})

add_custom_target(smtrat DEPENDS smtrat-shared)
if (STATICLIB_SWITCH)
	add_dependencies(smtrat smtrat-static)
endif()

