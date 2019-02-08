file(GLOB_RECURSE test_sources "*.cpp")
add_executable(runNLSATTests ${test_sources})

target_link_libraries(runNLSATTests
	${Boost_unit_test_framework_SHARED}
	smtrat-mcsat-shared
)
add_test(NAME nlsat COMMAND runNLSATTests)
