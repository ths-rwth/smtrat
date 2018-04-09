file(GLOB_RECURSE test_sources "*.cpp")

add_executable(runCADTests ${test_sources})

target_link_libraries(runCADTests libboost_unit_test_framework.a lib_${PROJECT_NAME} ${libraries})

add_test(NAME cad COMMAND runCADTests)
