file(GLOB_RECURSE test_sources "*.cpp")

add_executable(runCADTests ${test_sources})

target_link_libraries(runCADTests
    ${Boost_UNIT_TEST_FRAMEWORK_LIBRARY}
    lib_${PROJECT_NAME}
    ${libraries}
)

add_custom_target(check COMMAND ${CMAKE_CTEST_COMMAND} DEPENDS runCADTests)

add_test(NAME cad COMMAND runCADTests)
