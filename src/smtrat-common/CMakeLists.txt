include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

get_cmake_property(variableNames VARIABLES)
set(VARLIST "")
foreach (variableName ${variableNames})
	get_property(ISADV CACHE ${variableName} PROPERTY ADVANCED SET)
	get_property(TYPE CACHE ${variableName} PROPERTY TYPE)
	set(VARLIST "${VARLIST}\n\tprint(${ISADV}, \"${TYPE}\", \"${variableName}\", R\"VAR(${${variableName}})VAR\");")
endforeach()

configure_everything()

file(GLOB_RECURSE smtrat-common_sources "*.cpp")

add_new_libraries(smtrat-common ${PROJECT_VERSION} "${smtrat-common_sources}" "resources")
target_include_dirs_from(smtrat-common-objects "" PUBLIC carl-shared)
target_link_libraries(smtrat-common-shared carl-shared)
target_link_libraries(smtrat-common-static carl-static)

install_libraries(smtrat-common-shared smtrat-common-static)
