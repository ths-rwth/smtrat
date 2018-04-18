add_executable( runDatastructuresTests
	Test_datastructures.cpp
)
cotire(runDatastructuresTests)
target_link_libraries(runDatastructuresTests
    ${Boost_UNIT_TEST_FRAMEWORK_LIBRARY}
    lib_${PROJECT_NAME}
    ${libraries})

add_test( NAME datastructures COMMAND runDatastructuresTests )
