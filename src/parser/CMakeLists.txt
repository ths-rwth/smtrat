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
# Version: 2012-07-06                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

include_directories( ${CMAKE_SOURCE_DIR}/src
					 ${CMAKE_SOURCE_DIR}/src/parser
					 ${CMAKE_BINARY_DIR}/src/parser )


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

# Create executable solver
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

# Other libraries that are used by the project library should go here.
target_link_libraries( smtratSolver 
		       lib_${PROJECT_NAME}
		       ${libraries} )

if(${STATICLIB_SWITCH} STREQUAL "ON")
  set_target_properties( smtratSolver PROPERTIES LINK_SEARCH_END_STATIC TRUE )
endif()

