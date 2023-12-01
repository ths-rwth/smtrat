file(GLOB_RECURSE test_sources "*.cpp")

add_executable(runQuantifierCoveringTest ${test_sources})

target_link_libraries(runQuantifierCoveringTest smtrat-coveringng-shared ${GTEST_LIBRARIES})

add_test(NAME quantifierCovering COMMAND runQuantifierCoveringTest)
add_dependencies(all-tests runQuantifierCoveringTest)
