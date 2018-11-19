set(LIB_VERSION "${PROJECT_VERSION_MAJOR}.${PROJECT_VERSION_MINOR}")

file(GLOB_RECURSE smtrat-qe_tpl "*.in")
foreach(tpl ${smtrat-qe_tpl})
	string(REGEX REPLACE ".in$" "" file ${tpl})
	configure_file("${tpl}" "${file}")
endforeach()

file(GLOB_RECURSE smtrat-qe_sources "*.cpp")

add_library(smtrat-qe-shared SHARED ${smtrat-qe_sources})
add_dependencies(smtrat-qe-shared resources lib_smtrat)
set_target_properties(smtrat-qe-shared PROPERTIES
	VERSION "${LIB_VERSION}"
	SOVERSION "${LIB_VERSION}"
	CLEAN_DIRECT_OUTPUT 1
	OUTPUT_NAME smtrat-qe
	LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}
	ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}
)
target_link_libraries(smtrat-qe-shared lib_smtrat)

add_library(smtrat-qe-static STATIC ${smtrat-qe_sources})
add_dependencies(smtrat-qe-static resources)
set_target_properties(smtrat-qe-static PROPERTIES
	VERSION "${LIB_VERSION}"
	SOVERSION "${LIB_VERSION}"
	CLEAN_DIRECT_OUTPUT 1
	OUTPUT_NAME smtrat-qe
	LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}
	ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}
)
target_link_libraries(smtrat-qe-static lib_smtrat)

add_custom_target(smtrat-qe
	DEPENDS smtrat-qe-shared
	DEPENDS smtrat-qe-static
)
