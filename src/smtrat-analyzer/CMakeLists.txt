include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

configure_everything()

file(GLOB_RECURSE smtrat-analyzer_sources "*.cpp")

add_new_libraries(smtrat-analyzer "${PROJECT_VERSION_LIB}" "${smtrat-analyzer_sources}" "resources")
target_include_dirs_from(smtrat-analyzer-objects "" PUBLIC smtrat-cad-shared smtrat-common-shared)
target_link_libraries(smtrat-analyzer-shared smtrat-cad-shared smtrat-common-shared)
target_link_libraries(smtrat-analyzer-static smtrat-cad-static smtrat-common-static)

install_libraries(smtrat smtrat-analyzer-shared smtrat-analyzer-static)
