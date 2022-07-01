include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

configure_everything()

file(GLOB_RECURSE smtrat-max-smt_sources "*.cpp")

add_new_libraries(smtrat-max-smt ${PROJECT_VERSION_LIB} "${smtrat-max-smt_sources}" "resources")
target_include_dirs_from(smtrat-max-smt-objects "" PUBLIC smtrat-common-shared carl-arith-shared)
target_link_libraries(smtrat-max-smt-shared smtrat-common-shared carl-arith-shared)
target_link_libraries(smtrat-max-smt-static smtrat-common-static carl-arith-static)

install_libraries(smtrat smtrat-max-smt-shared smtrat-max-smt-static)

