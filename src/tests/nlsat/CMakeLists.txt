file(GLOB_RECURSE test_sources "*.cpp")
add_executable(runNLSATTests ${test_sources})

target_link_libraries(runNLSATTests
    ${Boost_UNIT_TEST_FRAMEWORK_LIBRARY}
    lib_${PROJECT_NAME}
    ${libraries}
)
add_test(NAME nlsat COMMAND runNLSATTests)
