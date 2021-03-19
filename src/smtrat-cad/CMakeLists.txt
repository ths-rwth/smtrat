include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

configure_everything()

file(GLOB_RECURSE smtrat-cad_sources "*.cpp")

add_new_libraries(smtrat-cad "${PROJECT_VERSION_LIB}" "${smtrat-cad_sources}" "resources")
target_include_dirs_from(smtrat-cad-objects "" PUBLIC smtrat-common-shared smtrat-variablebounds-shared carl-covering-shared carl-model-shared)
target_link_libraries(smtrat-cad-shared smtrat-common-shared smtrat-variablebounds-shared carl-covering-shared carl-model-shared)
target_link_libraries(smtrat-cad-static smtrat-common-static smtrat-variablebounds-static carl-covering-static carl-model-static)

install_libraries(smtrat smtrat-cad-shared smtrat-cad-static)
