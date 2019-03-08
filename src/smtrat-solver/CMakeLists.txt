include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

configure_everything()

file(GLOB_RECURSE smtrat-solver_sources "*.cpp")

add_new_libraries(smtrat-solver "${PROJECT_VERSION_LIB}" "${smtrat-solver_sources}" "resources")
target_include_dirs_from(smtrat-solver-objects "" PUBLIC smtrat-lib-shared smtrat-common-shared)
target_link_libraries(smtrat-solver-shared smtrat-lib-shared smtrat-common-shared)
target_link_libraries(smtrat-solver-static smtrat-lib-static smtrat-common-static)

install_libraries(smtrat smtrat-solver-shared smtrat-solver-static)
