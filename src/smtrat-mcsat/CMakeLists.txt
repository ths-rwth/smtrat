include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

configure_everything()

file(GLOB_RECURSE smtrat-mcsat_sources "*.cpp")

add_new_libraries(smtrat-mcsat "${PROJECT_VERSION_LIB}" "${smtrat-mcsat_sources}" "resources")
target_include_dirs_from(smtrat-mcsat-objects "" PUBLIC smtrat-common-shared)
target_link_libraries(smtrat-mcsat-shared
	smtrat-common-shared
	smtrat-solver-shared
	smtrat-module-LRAModule-LRASettings1-shared
	smtrat-cadcells-shared
	rt
)
target_link_libraries(smtrat-mcsat-static
	smtrat-common-static
	smtrat-solver-static
	smtrat-module-LRAModule-static
	smtrat-cadcells-static
	rt
)

install_libraries(smtrat smtrat-mcsat-shared smtrat-mcsat-static)
