file(GLOB_RECURSE test_sources "*.cpp")
add_executable(runMCSATTests ${test_sources})

target_link_libraries(runMCSATTests
	Boost_unit_test_framework_SHARED
	smtrat-mcsat-shared
)
add_test(NAME mcsat COMMAND runMCSATTests)
