include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

configure_everything()

file(GLOB_RECURSE smtrat_lib_sources "*.cpp")

add_new_libraries(smtrat-lib ${PROJECT_VERSION_LIB} "${smtrat_lib_sources}" "resources")
target_include_dirs_from(smtrat-lib-objects "" PUBLIC smtrat-common-shared carl-shared)
target_link_libraries(smtrat-lib-shared smtrat-common-shared carl-shared)
target_link_libraries(smtrat-lib-static smtrat-common-static carl-static)

install_libraries(smtrat-lib-shared smtrat-lib-static)

if (CLANG_TIDY)
	add_custom_target(tidy
		COMMAND clang-tidy -p ${CMAKE_BINARY_DIR}/compile_commands.json ${CLANG_TIDY_CHECKS} -header-filter='.*' ${smtrat_lib_sources}
		WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/src/lib/
	)
	file(GLOB dirs LIST_DIRECTORIES true RELATIVE "${CMAKE_SOURCE_DIR}/src/lib/" "*")
	foreach(dir ${dirs})
		if(IS_DIRECTORY "${CMAKE_SOURCE_DIR}/src/lib/${dir}")
			file(GLOB_RECURSE sources_${dir} "${CMAKE_SOURCE_DIR}/src/lib/${dir}/*.cpp")
			add_custom_target(tidy-${dir}
				COMMAND ${CLANG_TIDY} -p ../../build/compile_commands.json ${CLANG_TIDY_CHECKS} -header-filter='.*' ${sources_${dir}}
				WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/src/lib/
			)
		endif()
	endforeach()
endif()