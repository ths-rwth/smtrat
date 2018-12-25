include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

configure_everything()

file(GLOB_RECURSE smtrat-wrapper_sources "*.cpp")

add_new_libraries(smtrat-wrapper ${PROJECT_VERSION} "${smtrat-wrapper_sources}" "resources")
target_include_dirs_from(smtrat-wrapper-objects "" PUBLIC smtrat-common-shared carl-shared)
target_link_libraries(smtrat-wrapper-shared lib_smtrat smtrat-common-shared smtrat-modules-shared smtrat-strategies-shared)
target_link_libraries(smtrat-wrapper-static lib_smtrat smtrat-common-static smtrat-modules-static smtrat-strategies-static)

install_libraries(smtrat-wrapper-shared smtrat-wrapper-static)

