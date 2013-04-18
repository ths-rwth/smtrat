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
# Version: 2012-10-10                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

#TODO: are all these directories really necessary?
include_directories(${CMAKE_SOURCE_DIR}/src
					 ${CMAKE_SOURCE_DIR}/src/solver
					 ${CMAKE_SOURCE_DIR}/src/solver/parser
					 ${CMAKE_BINARY_DIR}/src/solver
					 ${CMAKE_BINARY_DIR}/src/solver/parser
					${GINACRA_INCLUDE_DIR}
 )

#TODO: we only link against the library, which is copied to the binary root dir. We should somehow save that in a variable.
link_directories( ${PROJECT_BINARY_DIR}/src/lib
                  ${PROJECT_BINARY_DIR} )

# Create custom command for flex/lex (note the outputs)
add_custom_command( OUTPUT ${CMAKE_BINARY_DIR}/src/solver/Parser.tab.cc
	COMMAND ${BISON_EXECUTABLE}
	ARGS ${CMAKE_SOURCE_DIR}/src/solver/parser/Parser.yy
)

# Create custom command for flex/lex (note the outputs)
add_custom_command( OUTPUT ${CMAKE_BINARY_DIR}/src/solver/lex.smtrat.cc
	COMMAND ${FLEX_EXECUTABLE}
	ARGS ${CMAKE_SOURCE_DIR}/src/solver/parser/Scanner.ll
)

# executable solver
# # # # # # # # # #

add_executable( smtratSolver
	${CMAKE_SOURCE_DIR}/src/solver/parser/Driver.cc
	smtratSolver.cpp
	${CMAKE_BINARY_DIR}/src/solver/Parser.tab.cc
	${CMAKE_BINARY_DIR}/src/solver/lex.smtrat.cc
	RuntimeSettingsManager.cpp
)

#TODO: Dependencies do not work correctly, rebuilding parser is not triggered!
add_dependencies( smtratSolver
	${CMAKE_BINARY_DIR}/src/solver/parser/Scanner.ll
	${CMAKE_BINARY_DIR}/src/solver/parser/Parser.yy
)
target_link_libraries( smtratSolver
						lib_${PROJECT_NAME} # smtrat library
						${libraries} # libraries definied in top-level CMakeLists.txt
)
set_target_properties( smtratSolver PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR} )
if(${STATICLIB_SWITCH} STREQUAL "ON")
  set_target_properties( smtratSolver PROPERTIES LINK_SEARCH_END_STATIC TRUE )
  set_target_properties( smtratSolver PROPERTIES LINK_SEARCH_START_STATIC TRUE )
endif()

add_library( smtlibParser
	${CMAKE_SOURCE_DIR}/src/solver/parser/Driver.cc
	${CMAKE_SOURCE_DIR}/src/solver/smtratSolver.cpp
	${CMAKE_BINARY_DIR}/src/solver/Parser.tab.cc
	${CMAKE_BINARY_DIR}/src/solver/lex.smtrat.cc
	${CMAKE_SOURCE_DIR}/src/lib/Formula.cpp
	${CMAKE_SOURCE_DIR}/src/lib/ConstraintPool.cpp
	${CMAKE_SOURCE_DIR}/src/lib/Constraint.cpp
)

# add linking libraries. This is an over-approximation.
target_link_libraries( smtlibParser ${libraries})

if(${STATICLIB_SWITCH} STREQUAL "ON")
  set_target_properties( smtlibParser PROPERTIES LINK_SEARCH_START_STATIC TRUE )
  set_target_properties( smtlibParser PROPERTIES LINK_SEARCH_END_STATIC TRUE )
endif()

set_target_properties( smtlibParser PROPERTIES
		# create *nix style library versions + symbolic links
		VERSION "${${PROJECT_NAME}_MAJORVERSION}.${${PROJECT_NAME}_MINORVERSION}.${${PROJECT_NAME}_MAINTENANCEVERSION}"
		SOVERSION "${${PROJECT_NAME}_MAJORVERSION}.${${PROJECT_NAME}_MINORVERSION}.${${PROJECT_NAME}_MAINTENANCEVERSION}"
		# allow creating static and shared libs without conflicts
		# CLEAN_DIRECT_OUTPUT 1
		# avoid conflicts between library and binary target names
)
