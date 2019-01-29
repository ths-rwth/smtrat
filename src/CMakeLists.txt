# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#                                                             #
# File: src/CMakeLists.txt                                    #
#                                                             #
# Project name: SMT-RAT                                       #
# Contact: Florian Corzilius <corzilius@cs.rwth-aachen.de>,   #
#          Ulrich Loup <loup@cs.rwth-aachen.de>               #
# Project page: https://github.com/smtrat/smtrat/wiki         #
# Development status: beta                                    #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# Version: 2013-04-18                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #


add_subdirectory(smtrat-common)
add_subdirectory(lib)
add_subdirectory(smtrat-cad)
add_subdirectory(smtrat-mcsat)
add_subdirectory(smtrat-modules)
add_subdirectory(smtrat-qe)
add_subdirectory(smtrat-solver)
add_subdirectory(smtrat-strategies)
add_subdirectory(smtrat-unsat-cores)
add_subdirectory(smtrat-wrapper)

if(BUILD_SOLVER)
	add_subdirectory(cli)
endif()
# unit tests
# # # # # # #

add_subdirectory(benchmax EXCLUDE_FROM_ALL)

if (ENABLE_TESTING)
    # only build tests if we want them to be built. Do not exclude from all target, since
    # make test won't build the tests for us!
    add_subdirectory(tests)
endif()

add_subdirectory(gui EXCLUDE_FROM_ALL)

add_subdirectory(delta)

if (CLANG_TIDY)
	file(GLOB dirs LIST_DIRECTORIES true RELATIVE "${CMAKE_SOURCE_DIR}/src/" "*")
	foreach(dir ${dirs})
		if(IS_DIRECTORY "${CMAKE_SOURCE_DIR}/src/${dir}")
			file(GLOB_RECURSE sources_${dir} "${CMAKE_SOURCE_DIR}/src/${dir}/*.cpp")
			add_custom_target(tidy-${dir}
				COMMAND ${CLANG_TIDY} -p ../../build/compile_commands.json ${CLANG_TIDY_CHECKS} -header-filter='.*' ${sources_${dir}}
				WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/src/lib/
			)
		endif()
	endforeach()
endif()