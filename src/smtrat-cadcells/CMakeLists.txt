include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

configure_everything()

file(GLOB_RECURSE smtrat-cadcells_sources "*.cpp")

add_new_libraries(smtrat-cadcells "${PROJECT_VERSION_LIB}" "${smtrat-cadcells_sources}" "resources")
target_include_dirs_from(smtrat-cadcells-objects "" PUBLIC smtrat-common-shared carl-covering-shared carl-formula-shared)
target_link_libraries(smtrat-cadcells-shared smtrat-common-shared carl-covering-shared carl-formula-shared)
target_link_libraries(smtrat-cadcells-static smtrat-common-static carl-covering-static carl-formula-static)

install_libraries(smtrat smtrat-cadcells-shared smtrat-cadcells-static)
