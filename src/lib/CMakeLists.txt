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
message(${carl_INCLUDE_DIR})
if(ReallyNull_FOUND)
    include_directories( ${ReallyNull_INCLUDE_DIR} )
endif()

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
    Module.h
    Condition.h
    Formula.h
    StrategyGraph.h
    ModuleFactory.h
    ModuleType.h
    Common.h
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

# Include strategies
#######################
add_subdirectory(strategies)

# write config.h
#######################
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/config.h.in ${CMAKE_SOURCE_DIR}/src/lib/config.h )

# write CompileInfo.cpp
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/CompileInfo.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/CompileInfo.cpp )


set(lib_datastructures_headers
	datastructures/lra/Bound.hpp
	datastructures/lra/Tableau.hpp
	datastructures/lra/Value.hpp
	datastructures/lra/Variable.hpp
	datastructures/lra/Numeric.h
	datastructures/vs/SqrtEx.h
)
set(lib_datastructures_src
	datastructures/lra/Numeric.cpp
	datastructures/vs/SqrtEx.cpp
)

set(lib_misc_headers
	misc/VS_Tools.hpp
)
set(lib_misc_src
	misc/VS_Tools.cpp
)

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
    ${lib_datastructures_src}
    ${lib_misc_src}
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
target_link_libraries( lib_${PROJECT_NAME} lib_carl ${libraries} ) # libraries definied in top-level CMakeLists.txt


# Install destination and permissions for the library
# # # # # # # # # # # # # # # # # # # # # # # # # # #

install( TARGETS lib_${PROJECT_NAME} DESTINATION lib PERMISSIONS
    OWNER_READ OWNER_WRITE OWNER_EXECUTE
    GROUP_READ GROUP_EXECUTE
    WORLD_READ WORLD_EXECUTE
)
