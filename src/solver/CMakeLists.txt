# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#                                                             #
# File: src/solver/CMakeLists.txt                             #
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
                    ${CMAKE_BINARY_DIR}/src/solver
                    ${carl_INCLUDE_DIR}
 )

#TODO: we only link against the library, which is copied to the binary root dir. We should somehow save that in a variable.
link_directories( ${PROJECT_BINARY_DIR}/src/lib
                  ${PROJECT_BINARY_DIR} )

# write config.h
#######################
configure_file( ${CMAKE_SOURCE_DIR}/src/solver/config.h.in ${CMAKE_SOURCE_DIR}/src/solver/config.h )


# executable solver
# # # # # # # # # #

add_executable( smtratSolver
	${CMAKE_SOURCE_DIR}/src/solver/parser/Parser.cpp
	${CMAKE_SOURCE_DIR}/src/solver/parser/ParserUtils.cpp
        ${CMAKE_SOURCE_DIR}/src/solver/parser/Sort.cpp
	smtratSolver.cpp
	RuntimeSettingsManager.cpp
)

target_link_libraries( smtratSolver
                        lib_${PROJECT_NAME} # smtrat library
                        lib_carl # arithmetic library
                        ${libraries} # libraries definied in top-level CMakeLists.txt
)

if(${USE_GINAC} STREQUAL "ON")
  target_link_libraries( smtratSolver ginac ${libraries})
endif()
set_target_properties( smtratSolver PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR} )
if(${STATICLIB_SWITCH} STREQUAL "ON")
  set_target_properties( smtratSolver PROPERTIES LINK_SEARCH_END_STATIC TRUE )
  set_target_properties( smtratSolver PROPERTIES LINK_SEARCH_START_STATIC TRUE )
endif()

add_library( smtlibParser
	${CMAKE_SOURCE_DIR}/src/solver/smtratSolver.cpp
	${CMAKE_SOURCE_DIR}/src/lib/Formula.cpp
	${CMAKE_SOURCE_DIR}/src/lib/ConstraintPool.cpp
	${CMAKE_SOURCE_DIR}/src/lib/Constraint.cpp
)

# add linking libraries. This is an over-approximation.
target_link_libraries( smtlibParser lib_carl ${libraries})

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
