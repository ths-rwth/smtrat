include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

configure_everything()

file(GLOB_RECURSE smtrat-common_sources "*.cpp")

add_new_libraries(smtrat-common ${PROJECT_VERSION} "${smtrat-common_sources}" "resources")
target_link_libraries(smtrat-common-objects carl-shared)
target_link_libraries(smtrat-common-shared carl-shared)
target_link_libraries(smtrat-common-static carl-static)
