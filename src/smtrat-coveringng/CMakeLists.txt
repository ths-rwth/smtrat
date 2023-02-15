include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

configure_everything()

file(GLOB_RECURSE smtrat-coveringng_sources "*.cpp")

add_new_libraries(smtrat-coveringng "${PROJECT_VERSION_LIB}" "${smtrat-coveringng_sources}" "resources")
target_include_dirs_from(smtrat-coveringng-objects "" PUBLIC smtrat-common-shared smtrat-cadcells-shared)
target_link_libraries(smtrat-coveringng-shared smtrat-common-shared smtrat-cadcells-shared)
target_link_libraries(smtrat-coveringng-static smtrat-common-static smtrat-cadcells-static)

install_libraries(smtrat smtrat-coveringng-shared smtrat-coveringng-static)
