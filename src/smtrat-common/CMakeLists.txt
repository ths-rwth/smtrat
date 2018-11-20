include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)


file(GLOB_RECURSE smtrat-common_sources "*.cpp")

add_new_libraries(smtrat-common ${PROJECT_VERSION} "${smtrat-common_sources}" "resources")
target_link_libraries(smtrat-common-objects carl-shared)
target_link_libraries(smtrat-common-shared carl-shared)
target_link_libraries(smtrat-common-static carl-static)

get_cmake_property(variableNames VARIABLES)
set(VARLIST "")
foreach (variableName ${variableNames})
	get_property(ISADV CACHE ${variableName} PROPERTY ADVANCED SET)
	get_property(TYPE CACHE ${variableName} PROPERTY TYPE)
	if((NOT ${ISADV}) AND (NOT ${TYPE} MATCHES "INTERNAL") AND (NOT ${TYPE} MATCHES "STATIC"))
		set(VARLIST "${VARLIST}\n\tp(\"${variableName}\", R\"VAR(${${variableName}})VAR\");")
	endif()
endforeach()

configure_file(CompileInfo.cpp.in CompileInfo.cpp )
configure_everything()