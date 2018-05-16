file(GLOB_RECURSE test_sources "*.cpp")

add_executable(runPseudoBoolTests ${test_sources})

target_link_libraries(runPseudoBoolTests
    ${Boost_UNIT_TEST_FRAMEWORK_LIBRARY}
    lib_${PROJECT_NAME}
    ${libraries}
)

add_test(NAME pseudobool COMMAND runPseudoBoolTests)

