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
	VariableBounds.h
    smtrat.h
)

# Include modules
#######################
add_subdirectory(modules)

# Include solvers/strategies
#######################
add_subdirectory(strategies)


if(USE_GB)
	set(lib_GBModule_headers modules/GBModule/GBSettings.h modules/GBModule/GBModuleStatistics.h modules/GBModule/GBCalculationStatistics.h)
	set(lib_GBModule_src modules/GBModule/GBModuleStatistics.cpp modules/GBModule/GBCalculationStatistics.cpp)
	set(lib_modules_headers ${lib_modules_headers} modules/GroebnerModule.h modules/GroebnerModule.tpp)
endif()

if(USE_CAD)
	set(lib_modules_headers ${lib_modules_headers} modules/CADModule.h)
	set(lib_modules_src ${lib_modules_src}  modules/CADModule.cpp)
endif()

set(lib_VSModule_headers
    modules/VSModule/Condition.h
    modules/VSModule/SqrtEx.h
    modules/VSModule/State.h
    modules/VSModule/Substitute.h
    modules/VSModule/Substitution.h
    modules/VSModule/Tools.h
)
set(lib_VSModule_src
    modules/VSModule/Condition.cpp
    modules/VSModule/SqrtEx.cpp
    modules/VSModule/State.cpp
    modules/VSModule/Substitute.cpp
    modules/VSModule/Substitution.cpp
)
set(lib_SingleVSModule_headers
    modules/SingleVSModule/Substitute.h
)

set(lib_SingleVSModule_src
    modules/SingleVSModule/Substitute.cpp
)
set(lib_SATModule_headers
	modules/SATModule/Alg.h
	modules/SATModule/Alloc.h
	modules/SATModule/Heap.h
	modules/SATModule/IntTypes.h
	modules/SATModule/Map.h
	modules/SATModule/Queue.h
	modules/SATModule/Sort.h
	modules/SATModule/Vec.h
	modules/SATModule/XAlloc.h
	modules/SATModule/Options.h
	modules/SATModule/SolverTypes.h
	modules/SATModule/SATStatistics.h
)
set(lib_SATModule_src
	modules/SATModule/Options.cpp
	modules/SATModule/SATStatistics.cpp
)
set(lib_LRAModule_headers
	modules/LRAModule/Bound.h
	modules/LRAModule/Tableau.h
	modules/LRAModule/Value.h
	modules/LRAModule/Variable.h
)
set(lib_LRAModule_src
	modules/LRAModule/Bound.cpp
	modules/LRAModule/Tableau.cpp
	modules/LRAModule/Value.cpp
	modules/LRAModule/Variable.cpp
)
set(lib_TLRAModule_headers
	modules/TLRAModule/Bound.h
	modules/TLRAModule/Tableau.h
	modules/TLRAModule/Value.h
	modules/TLRAModule/Variable.h
	modules/TLRAModule/Numeric.h
)
set(lib_TLRAModule_src
	modules/TLRAModule/Numeric.cpp
)
set(lib_ICPModule_headers
    modules/ICPModule/DerivativeTable.h
)
set(lib_ICPModule_src

)

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
)
set(lib_utilities_src
	utilities/stats/CollectStatistics.cpp
)


set( lib_nratsolver_headers NRATSolver.h )
set( lib_nratsolver_src NRATSolver.cpp )

set(lib_${PROJECT_NAME}_SRCS
    ${lib_nratsolver_src}
    ${lib_core_src}
    ${lib_modules_src}
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
#install( FILES ${lib_core_headers} ${lib_nratsolver_headers} DESTINATION include/${PROJECT_NAME}/lib )
#install( FILES ${lib_modules_headers} DESTINATION include/${PROJECT_NAME}/lib/modules )
#install( FILES ${lib_VSModule_headers} DESTINATION include/${PROJECT_NAME}/lib/modules/VSModule )
#install( FILES ${lib_SATModule_headers} DESTINATION include/${PROJECT_NAME}/lib/modules/SATModule )
#install( FILES ${lib_LRAModule_headers} DESTINATION include/${PROJECT_NAME}/lib/modules/LRAModule )
#install( FILES ${lib_SingleVSModule_headers} DESTINATION include/${PROJECT_NAME}/lib/modules/SingleVSModule )
# install( FILES ${lib_ICPModule_headers} DESTINATION include/${PROJECT_NAME}/lib/modules/ICPModule )
#install( FILES ${lib_TLRAModule_headers} DESTINATION include/${PROJECT_NAME}/lib/modules/TLRAModule )
