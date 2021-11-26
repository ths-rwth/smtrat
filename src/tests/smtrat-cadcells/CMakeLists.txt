file(GLOB_RECURSE test_sources "*.cpp")

add_executable(runCadcellsTest ${test_sources})

target_link_libraries(runCadcellsTest smtrat-cadcells-shared ${GTEST_LIBRARIES})

add_test(NAME cadcells COMMAND runCadcellsTest)
add_dependencies(all-tests runCadcellsTest)
