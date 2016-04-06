# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#                                                             #
# File: src/utilities/CMakeLists.txt                          #
#                                                             #
# Project name: SMT-RAT                                       #
# Contact: Florian Corzilius <corzilius@cs.rwth-aachen.de>,   #
#          Ulrich Loup <loup@cs.rwth-aachen.de>               #
# Project page: https://github.com/smtrat/smtrat/wiki         #
# Development status: beta                                    #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# Version: 2013-03-31                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #


get_cmake_property(variableNames VARIABLES)
set(VARLIST "")
foreach (variableName ${variableNames})
	get_property(ISADV CACHE ${variableName} PROPERTY ADVANCED SET)
	get_property(TYPE CACHE ${variableName} PROPERTY TYPE)
	if((NOT ${ISADV}) AND (NOT ${TYPE} MATCHES "INTERNAL") AND (NOT ${TYPE} MATCHES "STATIC"))
		set(VARLIST "${VARLIST}\n\tp(\"${variableName}\", R\"VAR(${${variableName}})VAR\");")
	endif()
endforeach()

configure_file( ${CMAKE_SOURCE_DIR}/src/lib/utilities/CMakeOptions.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/utilities/CMakeOptions.cpp )
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/utilities/CompileInfo.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/utilities/CompileInfo.cpp )
