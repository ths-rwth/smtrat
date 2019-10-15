include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

configure_everything()

file(GLOB_RECURSE smtrat-optimization_sources "*.cpp")

add_new_libraries(smtrat-optimization ${PROJECT_VERSION_LIB} "${smtrat-optimization_sources}" "resources")
target_include_dirs_from(smtrat-optimization-objects "" PUBLIC smtrat-common-shared carl-shared)
target_link_libraries(smtrat-optimization-shared smtrat-common-shared carl-shared)
target_link_libraries(smtrat-optimization-static smtrat-common-static carl-static)

install_libraries(smtrat smtrat-optimization-shared smtrat-optimization-static)

