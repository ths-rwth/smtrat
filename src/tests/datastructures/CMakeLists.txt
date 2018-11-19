add_executable( runDatastructuresTests
	Test_datastructures.cpp
)
cotire(runDatastructuresTests)
target_link_libraries(runDatastructuresTests
    ${Boost_unit_test_framework_SHARED}
    lib_${PROJECT_NAME}
    ${libraries})

add_test( NAME datastructures COMMAND runDatastructuresTests )
