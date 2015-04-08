# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#                                                             #
# File: src/cli/CMakeLists.txt                             #
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
                    ${CMAKE_SOURCE_DIR}/src/cli
                    ${CMAKE_BINARY_DIR}/src/cli
                    ${carl_INCLUDE_DIR}
 )

#TODO: we only link against the library, which is copied to the binary root dir. We should somehow save that in a variable.
link_directories( ${PROJECT_BINARY_DIR}/src/lib
                  ${PROJECT_BINARY_DIR} )

# write config.h
#######################
configure_file( ${CMAKE_SOURCE_DIR}/src/cli/config.h.in ${CMAKE_SOURCE_DIR}/src/cli/config.h )


# executable solver
# # # # # # # # # #

add_executable( smtratSolver
    newparser/theories/Arithmetic.cpp
	newparser/theories/Bitvector.cpp
    newparser/theories/Core.cpp
    newparser/theories/Uninterpreted.cpp
	smtratSolver.cpp
	RuntimeSettingsManager.cpp
)

target_link_libraries( smtratSolver
                        lib_${PROJECT_NAME} # smtrat library
                        ${libraries} # libraries definied in top-level CMakeLists.txt
)

if(${USE_GINAC} STREQUAL "ON")
	target_link_libraries( smtratSolver ginac)
endif()
set_target_properties( smtratSolver PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR} )

add_library( smtlibParser
	${CMAKE_SOURCE_DIR}/src/cli/smtratSolver.cpp
)

# add linking libraries. This is an over-approximation.
target_link_libraries( smtlibParser ${libraries})

set_target_properties( smtlibParser PROPERTIES
		# create *nix style library versions + symbolic links
		VERSION "${${PROJECT_NAME}_MAJORVERSION}.${${PROJECT_NAME}_MINORVERSION}.${${PROJECT_NAME}_MAINTENANCEVERSION}"
		SOVERSION "${${PROJECT_NAME}_MAJORVERSION}.${${PROJECT_NAME}_MINORVERSION}.${${PROJECT_NAME}_MAINTENANCEVERSION}"
		# allow creating static and shared libs without conflicts
		# CLEAN_DIRECT_OUTPUT 1
		# avoid conflicts between library and binary target names
)
