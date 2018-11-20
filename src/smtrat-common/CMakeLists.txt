include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

file(GLOB_RECURSE smtrat-common_tpl "*.in")
foreach(tpl ${smtrat-common_tpl})
	string(REGEX REPLACE ".in$" "" file ${tpl})
	configure_file("${tpl}" "${file}")
endforeach()

file(GLOB_RECURSE smtrat-common_sources "*.cpp")

add_new_libraries(smtrat-common ${PROJECT_VERSION} "${smtrat-common_sources}" "resources")
target_link_libraries(smtrat-common-objects lib_carl)
target_link_libraries(smtrat-common-shared lib_carl)
target_link_libraries(smtrat-common-static lib_carl_static)
