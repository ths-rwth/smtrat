# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#                                                             #
# File: src/parser/CMakeLists.txt                             #
#                                                             #
# Project name: SMT-RAT                                       #
# Contact: Florian Corzilius <corzilius@cs.rwth-aachen.de>,   #
#          Ulrich Loup <loup@cs.rwth-aachen.de>               #
# Project sourceforge page: http://smtrat.sourceforge.net/    #
# Development status: beta                                    #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# Version: 2012-07-30                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

include_directories( ${CMAKE_SOURCE_DIR}/src
					 ${CMAKE_SOURCE_DIR}/src/parser
					 ${CMAKE_BINARY_DIR}/src/parser )

link_directories( ${PROJECT_BINARY_DIR}/src
                  ${PROJECT_BINARY_DIR} )

# Create custom command for flex/lex (note the outputs)
add_custom_command( OUTPUT ${CMAKE_BINARY_DIR}/src/parser/Parser.tab.cc
	COMMAND ${BISON_EXECUTABLE}
	ARGS ${CMAKE_SOURCE_DIR}/src/parser/Parser.yy
)

# Create custom command for flex/lex (note the outputs)
add_custom_command( OUTPUT ${CMAKE_BINARY_DIR}/src/parser/lex.smtrat.cc
	COMMAND ${FLEX_EXECUTABLE}
	ARGS ${CMAKE_SOURCE_DIR}/src/parser/Scanner.ll
)

# executable solver
# # # # # # # # # #

add_executable( smtratSolver
	${CMAKE_BINARY_DIR}/src/parser/lex.smtrat.cc
	${CMAKE_SOURCE_DIR}/src/parser/Driver.cc
	${CMAKE_SOURCE_DIR}/src/NRATSolver.cpp
	${CMAKE_SOURCE_DIR}/src/smtratSolver.cpp
	${CMAKE_BINARY_DIR}/src/parser/Parser.tab.cc
)
add_dependencies( smtratSolver
	${CMAKE_BINARY_DIR}/src/parser/lex.smtrat.cc
	${CMAKE_SOURCE_DIR}/src/parser/Driver.cc
	${CMAKE_SOURCE_DIR}/src/NRATSolver.cpp
	${CMAKE_SOURCE_DIR}/src/smtratSolver.cpp
	${CMAKE_BINARY_DIR}/src/parser/Parser.tab.cc
)
target_link_libraries( smtratSolver
		       lib_${PROJECT_NAME}
		       ${libraries} # libraries definied in top-level CMakeLists.txt
)
set_target_properties( smtratSolver PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR} )
if(${STATICLIB_SWITCH} STREQUAL "ON")
  set_target_properties( smtratSolver PROPERTIES LINK_SEARCH_END_STATIC TRUE )
endif()
