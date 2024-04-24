include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)

configure_everything()

file(GLOB_RECURSE smtrat-fmplex_sources "*.cpp")

add_new_libraries(smtrat-fmplex "${PROJECT_VERSION_LIB}" "${smtrat-fmplex_sources}" "resources")
target_include_dirs_from(smtrat-fmplex-objects "" PUBLIC carl-formula-shared carl-arith-shared)
target_link_libraries(smtrat-fmplex-shared carl-formula-shared carl-arith-shared)
target_link_libraries(smtrat-fmplex-static carl-formula-static carl-arith-static)

install_libraries(smtrat smtrat-fmplex-shared smtrat-fmplex-static)
