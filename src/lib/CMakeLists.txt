# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#                                                             #
# File: src/CMakeLists.txt                                    #
#                                                             #
# Project name: SMT-RAT                                       #
# Contact: Florian Corzilius <corzilius@cs.rwth-aachen.de>,   #
#          Ulrich Loup <loup@cs.rwth-aachen.de>               #
# Project sourceforge page: http://smtrat.sourceforge.net/    #
# Development status: beta                                    #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# Version: 2012-10-22                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

include_directories( #${PROJECT_BUILD_DIR}/src
                     #${PROJECT_SOURCE_DIR}/src/parser
                     #${PROJECT_BUILD_DIR}/src/parser
                     ${GINACRA_INCLUDE_DIR}
)

# Core library
# # # # # # # # # # #
set(lib_core_src
    Manager.cpp
    Module.cpp
    Formula.cpp
    StrategyGraph.cpp
    Constraint.cpp
    ConstraintPool.cpp
	RuntimeSettings.cpp
        ThreadPool.cpp
	ValidationSettings.cpp
	CompileInfo.cpp
)

set(lib_core_headers
    Manager.h
    Answer.h
    Module.h
    Condition.h
    Formula.h
    StrategyGraph.h
    ModuleFactory.h
    ModuleType.h
    Constraint.h
    ConstraintPool.h
	RuntimeSettings.h
        ThreadPool.h
	VariableBounds.h
	ValidationSettings.h
    smtrat.h
)

# Include modules
#######################
add_subdirectory(modules)

# Include solvers/strategies
#######################
add_subdirectory(strategies)

# write config.h
#######################
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/config.h.in ${CMAKE_SOURCE_DIR}/src/lib/config.h )

# write CompileInfo.cpp
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/CompileInfo.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/CompileInfo.cpp )


# Nullstellensatz module variables

if(USE_NSS)
set(lib_NSSModule_headers
	modules/NSSModule/ConstraintMatrixFactory.h
	modules/NSSModule/GroebnerToSDP.h
	modules/NSSModule/MonomialIterator.h
)
set(lib_NSSModule_src
	modules/NSSModule/ConstraintMatrixFactory.cpp
	modules/NSSModule/MonomialIterator.cpp
)
set(lib_SDP_headers
	utilities/SDP/SDPFacade.h
	utilities/SDP/CSDPFacade.h
	utilities/SDP/SparseMatrix.h
)
set(lib_SDP_src
	utilities/SDP/CSDPFacade.cpp
	utilities/SDP/SparseMatrix.cpp
)
set(lib_LinAlg
	utilities/LinAlg/DenseMatrix.h
	utilities/LinAlg/FindExactSolution.h
)
endif()
set(lib_utilities_headers
	utilities/debug/debug.h
	utilities/stats/Statistics.h
	utilities/stats/CollectStatistics.h
	utilities/stats/StatisticSettings.h
)
set(lib_utilities_src
	utilities/stats/CollectStatistics.cpp
	utilities/stats/StatisticSettings.cpp
)

set(lib_${PROJECT_NAME}_SRCS
    ${lib_core_src}
    ${lib_modules_src}
    ${lib_strategies_src}
	${lib_utilities_src}
)

# set linking flags
# # # # # # # # # #

set(STATICLIB "SHARED")
if(${STATICLIB_SWITCH} STREQUAL "ON")
	set(STATICLIB "STATIC")
endif()

# library target
# # # # # # # # #

add_library(lib_${PROJECT_NAME} ${STATICLIB} ${lib_${PROJECT_NAME}_SRCS} )
target_link_libraries( lib_${PROJECT_NAME} ${libraries} ) # libraries definied in top-level CMakeLists.txt
set_target_properties( lib_${PROJECT_NAME} PROPERTIES
#		# create *nix style library versions + symbolic links
		VERSION "${${PROJECT_NAME}_MAJORVERSION}.${${PROJECT_NAME}_MINORVERSION}.${${PROJECT_NAME}_MAINTENANCEVERSION}"
		SOVERSION "${${PROJECT_NAME}_MAJORVERSION}.${${PROJECT_NAME}_MINORVERSION}.${${PROJECT_NAME}_MAINTENANCEVERSION}"
#		# allow creating static and shared libs without conflicts
#		# CLEAN_DIRECT_OUTPUT 1
#		# avoid conflicts between library and binary target names
		OUTPUT_NAME ${PROJECT_NAME}
        LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}
        ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}
)
if(${STATICLIB_SWITCH} STREQUAL "ON")
  set_target_properties( lib_${PROJECT_NAME} PROPERTIES LINK_SEARCH_END_STATIC TRUE )
  set_target_properties( lib_${PROJECT_NAME} PROPERTIES LINK_SEARCH_START_STATIC TRUE )
endif()
target_link_libraries( lib_${PROJECT_NAME} ${libraries} ) # libraries definied in top-level CMakeLists.txt


# Install destination and permissions for the library
# # # # # # # # # # # # # # # # # # # # # # # # # # #

install( TARGETS lib_${PROJECT_NAME} DESTINATION lib PERMISSIONS
    OWNER_READ OWNER_WRITE OWNER_EXECUTE
    GROUP_READ GROUP_EXECUTE
    WORLD_READ WORLD_EXECUTE
)
#install( FILES ${lib_modules_headers} DESTINATION include/${PROJECT_NAME}/lib/modules )
#install( FILES ${lib_VSModule_headers} DESTINATION include/${PROJECT_NAME}/lib/modules/VSModule )
#install( FILES ${lib_SATModule_headers} DESTINATION include/${PROJECT_NAME}/lib/modules/SATModule )
#install( FILES ${lib_LRAModule_headers} DESTINATION include/${PROJECT_NAME}/lib/modules/LRAModule )
#install( FILES ${lib_SingleVSModule_headers} DESTINATION include/${PROJECT_NAME}/lib/modules/SingleVSModule )
# install( FILES ${lib_ICPModule_headers} DESTINATION include/${PROJECT_NAME}/lib/modules/ICPModule )
#install( FILES ${lib_TLRAModule_headers} DESTINATION include/${PROJECT_NAME}/lib/modules/TLRAModule )