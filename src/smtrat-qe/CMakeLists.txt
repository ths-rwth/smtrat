set(LIB_VERSION "${PROJECT_VERSION_MAJOR}.${PROJECT_VERSION_MINOR}")

include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

file(GLOB_RECURSE smtrat-qe_tpl "*.in")
foreach(tpl ${smtrat-qe_tpl})
	string(REGEX REPLACE ".in$" "" file ${tpl})
	configure_file("${tpl}" "${file}")
endforeach()

file(GLOB_RECURSE smtrat-qe_sources "*.cpp")

add_new_libraries(smtrat-qe ${LIB_VERSION} "${smtrat-qe_sources}" "resources" "lib_smtrat")
