include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

configure_everything()

file(GLOB_RECURSE smtrat-strategies_sources "*.cpp")

add_new_libraries(smtrat-strategies "${PROJECT_VERSION_LIB}" "${smtrat-strategies_sources}" "resources")
target_include_dirs_from(smtrat-strategies-objects "" PUBLIC smtrat-solver-shared)
target_link_libraries(smtrat-strategies-shared smtrat-solver-shared)
target_link_libraries(smtrat-strategies-static smtrat-solver-static)

install_libraries(smtrat-strategies-shared smtrat-strategies-static)

file(GLOB strategies LIST_DIRECTORIES false RELATIVE ${CMAKE_CURRENT_SOURCE_DIR}/strategies/ strategies/*.h)
foreach(strategyfile ${strategies})
	get_filename_component(strategy ${strategyfile} NAME_WE)

	add_library(smtrat-strategy-${strategy}-shared INTERFACE)
	add_library(smtrat-strategy-${strategy}-static INTERFACE)
	install_libraries(smtrat-strategy-${strategy}-shared smtrat-strategy-${strategy}-static)

	file(READ "${CMAKE_CURRENT_SOURCE_DIR}/strategies/${strategyfile}" Content)
	string(REGEX MATCHALL "#include [<\"]smtrat-modules/[a-zA-Z]+Module/" Matches ${Content})
	string(REGEX MATCHALL "[a-zA-Z]+Module" Matches "${Matches}")

	foreach(module ${Matches})
		target_link_libraries(smtrat-strategy-${strategy}-shared INTERFACE smtrat-module-${module}-shared)
		target_link_libraries(smtrat-strategy-${strategy}-static INTERFACE smtrat-module-${module}-static)
	endforeach()

endforeach()