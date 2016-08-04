add_executable( runDatastructuresTests
	Test_datastructures.cpp
)
cotire(runDatastructuresTests)
target_link_libraries(runDatastructuresTests libboost_unit_test_framework.a lib_${PROJECT_NAME} ${libraries})

add_test( NAME datastructures COMMAND runDatastructuresTests )
