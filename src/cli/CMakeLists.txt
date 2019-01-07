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


add_executable( smtrat ${smtrat_cli_sources})

target_link_libraries( smtrat
                        lib_${PROJECT_NAME} # smtrat library
                        ${libraries} # libraries definied in top-level CMakeLists.txt
						smtrat-common-shared
						smtrat-modules-shared
						smtrat-qe-shared
						smtrat-unsat-cores-shared
						smtrat-strategy-${SMTRAT_Strategy}-shared
						smtrat-module-FPPModule-shared # for preprocessing
)

#if(USE_COTIRE)
#    cotire( smtrat )
#endif()

set_target_properties( smtrat PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR} )

if (CLANG_TIDY)
	add_custom_target(tidy-cli
		COMMAND clang-tidy -p ${CMAKE_BINARY_DIR}/compile_commands.json ${CLANG_TIDY_CHECKS} -header-filter='.*' ${smtrat_cli_sources}
		WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/src/cli/
	)
endif()


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
