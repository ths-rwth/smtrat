# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#                                                             #
# File: src/CMakeLists.txt                                    #
#                                                             #
# Project name: SMT-RAT                                       #
# Contact: Florian Corzilius <corzilius@cs.rwth-aachen.de>,   #
#          Ulrich Loup <loup@cs.rwth-aachen.de>               #
# Project page: https://github.com/smtrat/smtrat/wiki         #
# Development status: beta                                    #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# Version: 2013-03-31                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

# Configure all .in files
# Omit modules directories! (Special care is taken there)
# If modules/*.in is included here, this triggers rebuilds all the time.
file(GLOB_RECURSE smtrat_lib_tpl
	"datastructures/*.in"
	"solver/*.in"
	"strategies/*.in"
	"utilities/*.in"
	"config.h.in"
)
foreach(tpl ${smtrat_lib_tpl})
	string(REGEX REPLACE ".in$" "" file ${tpl})
	configure_file("${tpl}" "${file}")
endforeach()

add_subdirectory(modules)
add_subdirectory(utilities)

file(GLOB_RECURSE smtrat_lib_sources "*.cpp")

set(STATICLIB "SHARED")
if(STATICLIB_SWITCH)
	set(STATICLIB "STATIC")
endif()

# library target
# # # # # # # # #

add_library(lib_${PROJECT_NAME} ${STATICLIB} ${smtrat_lib_sources} )
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

set(SMTRAT_TARGETS lib_smtrat CACHE STRING INTERNAL FORCE)
target_link_libraries( lib_${PROJECT_NAME} ${libraries} ) # libraries defined in top-level CMakeLists.txt

target_include_directories( lib_${PROJECT_NAME} PUBLIC
	$<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>
	$<BUILD_INTERFACE:${CMAKE_SOURCE_DIR}/src>
)


if(USE_COTIRE)
    cotire( lib_${PROJECT_NAME} )
endif()




# Install destination and permissions for the library
# # # # # # # # # # # # # # # # # # # # # # # # # # #


install( TARGETS ${SMTRAT_TARGETS}
	EXPORT smtratTargets
	LIBRARY DESTINATION "${LIB_INSTALL_DIR}"
        ARCHIVE DESTINATION "${LIB_INSTALL_DIR}"
        COMPONENT shlib
	PERMISSIONS
		OWNER_READ OWNER_WRITE OWNER_EXECUTE
		GROUP_READ GROUP_EXECUTE
		WORLD_READ WORLD_EXECUTE
)
