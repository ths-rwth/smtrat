add_subdirectory(smtrat-common)
add_subdirectory(smtrat-analyzer)
add_subdirectory(smtrat-cad)
add_subdirectory(smtrat-cadcells)
add_subdirectory(smtrat-mcsat)
add_subdirectory(smtrat-modules)
add_subdirectory(smtrat-qe)
add_subdirectory(smtrat-solver)
add_subdirectory(smtrat-strategies)
add_subdirectory(smtrat-unsat-cores)
add_subdirectory(smtrat-max-smt)
add_subdirectory(smtrat-optimization)
add_subdirectory(smtrat-variablebounds)

if(BUILD_SOLVER)
	add_subdirectory(cli)
endif()
# unit tests
# # # # # # #

add_subdirectory(benchmax EXCLUDE_FROM_ALL)

add_subdirectory(tests)

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