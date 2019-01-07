include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

configure_everything()

file(GLOB_RECURSE smtrat-solver_sources "*.cpp")

add_new_libraries(smtrat-solver "${PROJECT_VERSION}" "${smtrat-solver_sources}" "resources")
target_include_dirs_from(smtrat-solver-objects "" PUBLIC lib_smtrat smtrat-common-shared)
target_link_libraries(smtrat-solver-shared lib_smtrat smtrat-common-shared)
target_link_libraries(smtrat-solver-static lib_smtrat smtrat-common-static)

install_libraries(smtrat-solver-shared smtrat-solver-static)
