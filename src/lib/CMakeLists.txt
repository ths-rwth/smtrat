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
# Version: 2013-03-31                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

include_directories( ${carl_INCLUDE_DIR} )
if(ReallyNull_FOUND)
    include_directories( ${ReallyNull_INCLUDE_DIR} )
endif()

# Core library
# # # # # # # # # # #
set(lib_core_src
    Formula.cpp
    Constraint.cpp
    ConstraintPool.cpp
    FormulaPool.cpp
    Sort.cpp
    SortManager.cpp
    UninterpretedFunction.cpp
    UFInstance.cpp
    UFInstancesManager.cpp
    UFManager.cpp
    VariablePool.cpp
)

set(lib_core_headers
    Condition.h
    Formula.h
    Common.h
    Constraint.h
    ConstraintPool.h
    FormulaPool.h
    VariablePool.h
    smtrat.h
    Sort.h
    SortManager.h
    UninterpretedEquality.h
    UninterpretedFunction.h
    UFInstance.h
    UFInstancesManager.h
    UFManager.h
    UninterpretedVariable.h
)

# Include modules
#######################
add_subdirectory(modules)

# Include strategies
#######################
add_subdirectory(strategies)

# write config.h
#######################
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/config.h.in ${CMAKE_SOURCE_DIR}/src/lib/config.h )

# write CompileInfo.cpp
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/solver/CompileInfo.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/solver/CompileInfo.cpp )


set(lib_datastructures_headers
        datastructures/Assignment.h
        datastructures/SortValue.h
        datastructures/SortValueManager.h
        datastructures/UFModel.h
        datastructures/VariableBounds.h
	datastructures/lra/Bound.h
	datastructures/lra/Tableau.h
	datastructures/lra/TableauSettings.h
	datastructures/lra/Value.h
	datastructures/lra/Variable.h
	datastructures/lra/Numeric.h
	datastructures/vs/SqrtEx.h
)

set(lib_datastructures_src
        datastructures/Assignment.cpp
        datastructures/SortValue.cpp
        datastructures/SortValueManager.cpp
        datastructures/UFModel.cpp
        datastructures/lra/Bound.tpp
	datastructures/lra/Numeric.cpp
	datastructures/lra/Tableau.tpp
	datastructures/lra/Value.tpp
	datastructures/lra/Variable.tpp
	datastructures/vs/SqrtEx.cpp
)

set(lib_solver_headers
	solver/debug.h
        solver/Manager.h
        solver/Module.h
        solver/ModuleInput.h
        solver/StrategyGraph.h
        solver/ModuleFactory.h
        solver/RuntimeSettings.h
        solver/ThreadPool.h
        solver/ValidationSettings.h
)

set(lib_solver_src
	solver/Manager.cpp
	solver/Module.cpp
	solver/ModuleInput.cpp
        solver/StrategyGraph.cpp
        solver/RuntimeSettings.cpp
        solver/ThreadPool.cpp
        solver/ValidationSettings.cpp
        solver/CompileInfo.cpp
)

set(lib_utilities_headers
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
    ${lib_datastructures_src}
    ${lib_modules_src}
    ${lib_solver_src}
    ${lib_strategies_src}
    ${lib_utilities_src}
)

# set linking flags
# # # # # # # # # #

set(STATICLIB "SHARED")
if(STATICLIB_SWITCH)
	set(STATICLIB "STATIC")
endif()

# library target
# # # # # # # # #

add_library(lib_${PROJECT_NAME} ${STATICLIB} ${lib_${PROJECT_NAME}_SRCS} )
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
if(STATICLIB_SWITCH)
	target_link_libraries( lib_${PROJECT_NAME} lib_carl_static ${libraries} ) # libraries definied in top-level CMakeLists.txt
else()
	target_link_libraries( lib_${PROJECT_NAME} lib_carl ${libraries} ) # libraries definied in top-level CMakeLists.txt
endif()


# Install destination and permissions for the library
# # # # # # # # # # # # # # # # # # # # # # # # # # #

install( TARGETS lib_${PROJECT_NAME} DESTINATION lib PERMISSIONS
    OWNER_READ OWNER_WRITE OWNER_EXECUTE
    GROUP_READ GROUP_EXECUTE
    WORLD_READ WORLD_EXECUTE
)
