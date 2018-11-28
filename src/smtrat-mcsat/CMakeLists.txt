include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

configure_everything()

file(GLOB_RECURSE smtrat-mcsat_sources "*.cpp")

add_new_libraries(smtrat-mcsat "${PROJECT_VERSION}" "${smtrat-mcsat_sources}" "resources")
target_include_dirs_from(smtrat-mcsat-objects "" PUBLIC smtrat-common-shared)
target_link_libraries(smtrat-mcsat-shared smtrat-common-shared)
target_link_libraries(smtrat-mcsat-static smtrat-common-static)

install_libraries(smtrat-mcsat-shared smtrat-mcsat-static)
