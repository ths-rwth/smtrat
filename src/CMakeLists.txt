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
# Version: 2012-05-21                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

set(lib_core_src
    Manager.cpp
    Module.cpp
    Formula.cpp
    Strategy.cpp
    Constraint.cpp
    ConstraintPool.cpp
)

set(lib_core_headers
    Manager.h
    Answer.h
    Module.h
    Condition.h
    Formula.h
    Strategy.h
    ModuleFactory.h
    ModuleType.h
    Constraint.h
    ConstraintPool.h
    smtrat.h
)

set(lib_modules_headers
    modules/Modules.h
    modules/StandardModuleFactory.h
    modules/SimplifierModule.h
    modules/VSModule.h
    modules/SATModule.h
    modules/LRAModule.h
    modules/LRAOneModule.h
    modules/LRATwoModule.h
    modules/PreProModule.h
    modules/CNFerModule.h
    modules/SingleVSModule.h
)

set(lib_modules_src
    modules/SimplifierModule.cpp
    modules/VSModule.cpp
    modules/SATModule.cpp
    modules/LRAModule.cpp
    modules/LRAOneModule.cpp
    modules/LRATwoModule.cpp
    modules/PreProModule.cpp
    modules/CNFerModule.cpp
    modules/SingleVSModule.cpp
)

if(USE_GB)
	set(lib_module_GBModule_headers modules/GBModule/InequalitiesTable.h modules/GBModule/GBSettings.h)

	set(lib_modules_headers ${lib_modules_headers} modules/GroebnerModule.h)
	set(lib_modules_src ${lib_modules_src}  modules/GroebnerModule.cpp)
endif()

if(USE_CAD)
	set(lib_modules_headers ${lib_modules_headers} modules/UnivariateCADModule.h modules/CADModule.h)
	set(lib_modules_src ${lib_modules_src}  modules/UnivariateCADModule.cpp modules/CADModule.cpp)
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
)

set(lib_SATModule_src
	modules/SATModule/Options.cpp
)

set(lib_LRAModule_headers
	modules/LRAModule/Delta.h
	modules/LRAModule/LAArray.h
	modules/LRAModule/LAColumn.h
	modules/LRAModule/LARow.h
	modules/LRAModule/LAVar.h
	modules/LRAModule/LRASolverA.h
)

set(lib_LRAModule_src
	modules/LRAModule/Delta.cpp
	modules/LRAModule/LAArray.cpp
	modules/LRAModule/LAColumn.cpp
	modules/LRAModule/LARow.cpp
	modules/LRAModule/LAVar.cpp
	modules/LRAModule/LRASolverA.cpp
)

set(lib_LRATwoModule_headers
    modules/LRATwoModule/BetaMap.h
    modules/LRATwoModule/Bound.h
    modules/LRATwoModule/BoundMap.h
    modules/LRATwoModule/EqualBound.h
    modules/LRATwoModule/LowerBound.h
    modules/LRATwoModule/Real.h
    modules/LRATwoModule/SimplexTableaux.h
    modules/LRATwoModule/UpperBound.h
)

set(lib_LRATwoModule_src
    modules/LRATwoModule/BetaMap.cpp
    modules/LRATwoModule/Bound.cpp
    modules/LRATwoModule/BoundMap.cpp
    modules/LRATwoModule/EqualBound.cpp
    modules/LRATwoModule/LowerBound.cpp
    modules/LRATwoModule/Real.cpp
    modules/LRATwoModule/SimplexTableaux.cpp
    modules/LRATwoModule/UpperBound.cpp
)

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
set(lib_Utilities
	utilities/debug/debug.h
)


set( lib_nratsolver_headers NRATSolver.h )
set( lib_nratsolver_src NRATSolver.cpp )

if(USE_CAD)
set( lib_nratsolvercadonly_headers NRATSolver_CADonly.h )
set( lib_nratsolvercadonly_src NRATSolver_CADonly.cpp )
endif()

add_subdirectory(${CMAKE_SOURCE_DIR}/src/parser)

set(lib_${PROJECT_NAME}_SRCS
    ${lib_nratsolver_headers}
    ${lib_nratsolver_src}
    ${lib_nratsolvercadonly_headers}
    ${lib_nratsolvercadonly_src}
    ${lib_core_headers}
    ${lib_core_src}
    ${lib_modules_headers}
    ${lib_modules_src}
    ${lib_VSModule_headers}
    ${lib_VSModule_src}
	${lib_SATModule_headers}
	${lib_SATModule_src}
	${lib_LRAModule_headers}
	${lib_LRAModule_src}
	${lib_LRAOneModule_headers}
	${lib_LRAOneModule_src}
	${lib_LRATwoModule_headers}
	${lib_LRATwoModule_src}
	${lib_GBModule_headers}
	${lib_NSSModule_headers}
	${lib_NSSModule_src}
	${lib_SDP_headers}
	${lib_SDP_src}
	${lib_LinAlg}
    ${lib_SingleVSModule_headers}
    ${lib_SingleVSModule_src}
)

set(STATICLIB "SHARED")
if(${STATICLIB_SWITCH} STREQUAL "ON")
	set(STATICLIB "STATIC")
endif()
add_library(lib_${PROJECT_NAME} ${STATICLIB} ${lib_${PROJECT_NAME}_SRCS} )

SET( libraries ${libraries}  ${cln_LIBRARIES} ${GINAC_LIBRARY} )

if(USE_GINACRA)
	SET( libraries ${libraries} ${GINACRA_LIBRARY} )
endif()

if(USE_NSS)
	add_library(csdp UNKNOWN IMPORTED)
	set_target_properties(csdp PROPERTIES IMPORTED_LOCATION "${PROJECT_SOURCE_DIR}/external/csdp/lib/libsdp.a")

	#Csdp should be automatically compiled whenever we compile smtrat
	add_dependencies(csdp csdp_lib)
	SET( libraries ${libraries} ${BLAS_LIBRARIES} ${LAPACK_LIBRARIES}  csdp )
endif()

# Other libraries that are used by the project library should go here.
target_link_libraries( lib_${PROJECT_NAME} ${libraries} )


set_target_properties( lib_${PROJECT_NAME} PROPERTIES
#		# create *nix style library versions + symbolic links
		VERSION "${${PROJECT_NAME}_MAJORVERSION}.${${PROJECT_NAME}_MINORVERSION}.${${PROJECT_NAME}_MAINTENANCEVERSION}"
		SOVERSION "${${PROJECT_NAME}_MAJORVERSION}.${${PROJECT_NAME}_MINORVERSION}.${${PROJECT_NAME}_MAINTENANCEVERSION}"
#		# allow creating static and shared libs without conflicts
#		# CLEAN_DIRECT_OUTPUT 1
#		# avoid conflicts between library and binary target names
		OUTPUT_NAME ${PROJECT_NAME}
)

#Set install destination and permissions for the library
install( TARGETS lib_${PROJECT_NAME} DESTINATION lib PERMISSIONS
    OWNER_READ OWNER_WRITE OWNER_EXECUTE
    GROUP_READ GROUP_EXECUTE
    WORLD_READ WORLD_EXECUTE )

install( FILES ${lib_core_headers} ${lib_nratsolver_headers} ${lib_nratsolvercadonly_headers} DESTINATION include/${PROJECT_NAME} )
install( FILES ${lib_modules_headers} DESTINATION include/${PROJECT_NAME}/modules)
install( FILES ${lib_VSModule_headers} DESTINATION include/${PROJECT_NAME}/modules/VSModule)
install( FILES ${lib_SATModule_headers} DESTINATION include/${PROJECT_NAME}/modules/SATModule)
install( FILES ${lib_LRAModule_headers} DESTINATION include/${PROJECT_NAME}/modules/LRAModule)
install( FILES ${lib_LRAOneModule_headers} DESTINATION include/${PROJECT_NAME}/modules/LRAOneModule)
install( FILES ${lib_LRATwoModule_headers} DESTINATION include/${PROJECT_NAME}/modules/LRATwoModule)
install( FILES ${lib_SingleVSModule_headers} DESTINATION include/${PROJECT_NAME}/modules/SingleVSModule)

if(CppUnit_FOUND)
add_subdirectory(test)
endif()
