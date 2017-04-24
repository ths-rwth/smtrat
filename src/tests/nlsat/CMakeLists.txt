file(GLOB_RECURSE test_sources "*.cpp")
add_executable(runNLSATTests ${test_sources})

target_link_libraries(runNLSATTests libboost_unit_test_framework.a lib_${PROJECT_NAME} ${libraries})
add_test(NAME nlsat COMMAND runNLSATTests)
