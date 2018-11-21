include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

configure_everything()

file(GLOB_RECURSE smtrat-qe_sources "*.cpp")

add_new_libraries(smtrat-qe "${PROJECT_VERSION}" "${smtrat-qe_sources}" "resources")
target_include_dirs_from(smtrat-qe-objects "" PUBLIC lib_smtrat smtrat-common-shared)
target_link_libraries(smtrat-qe-shared lib_smtrat smtrat-common-shared)
target_link_libraries(smtrat-qe-static lib_smtrat smtrat-common-static)
