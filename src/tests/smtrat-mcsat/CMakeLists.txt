file(GLOB_RECURSE test_sources "*.cpp")

add_executable(runMcsatTest ${test_sources})

target_link_libraries(runMcsatTest smtrat-mcsat-shared ${GTEST_LIBRARIES})

add_test(NAME mcsat COMMAND runMcsatTest)
add_dependencies(all-tests runMcsatTest)
