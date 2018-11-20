include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

file(GLOB_RECURSE smtrat-qe_tpl "*.in")
foreach(tpl ${smtrat-qe_tpl})
	string(REGEX REPLACE ".in$" "" file ${tpl})
	configure_file("${tpl}" "${file}")
endforeach()

file(GLOB_RECURSE smtrat-qe_sources "*.cpp")

add_new_libraries(smtrat-qe "${PROJECT_VERSION}" "${smtrat-qe_sources}" "resources")
target_link_libraries(smtrat-qe-objects lib_smtrat smtrat-common-shared)
target_link_libraries(smtrat-qe-shared lib_smtrat smtrat-common-shared)
target_link_libraries(smtrat-qe-static lib_smtrat smtrat-common-static)
