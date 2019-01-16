file(GLOB_RECURSE test_sources "*.cpp")

add_executable(runPseudoBoolTests ${test_sources})

target_link_libraries(runPseudoBoolTests
    ${Boost_unit_test_framework_SHARED}
	lib_${PROJECT_NAME}
    ${libraries}
	smtrat-module-PBPPModule-shared
)

add_test(NAME pseudobool COMMAND runPseudoBoolTests)

