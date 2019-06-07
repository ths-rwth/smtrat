add_executable( runDatastructuresTests
	Test_datastructures.cpp
	Test_Settings.cpp
)
cotire(runDatastructuresTests)
target_link_libraries(runDatastructuresTests
	Boost_unit_test_framework_SHARED
	smtrat-common-shared
)

add_test( NAME datastructures COMMAND runDatastructuresTests )
