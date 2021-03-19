include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

configure_everything()

file(GLOB_RECURSE smtrat-variablebounds_sources "*.cpp")

add_new_libraries(smtrat-variablebounds ${PROJECT_VERSION_LIB} "${smtrat-variablebounds_sources}" "resources")
target_include_dirs_from(smtrat-variablebounds-objects "" PUBLIC smtrat-common-shared carl-shared carl-covering-shared)
target_link_libraries(smtrat-variablebounds-shared smtrat-common-shared carl-shared carl-covering-shared)
target_link_libraries(smtrat-variablebounds-static smtrat-common-static carl-static carl-covering-static)

install_libraries(smtrat smtrat-variablebounds-shared smtrat-variablebounds-static)

