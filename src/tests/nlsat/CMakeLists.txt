add_executable( runNLSATTests
	Test_NLSAT.cpp
	Test_AssignmentGenerator.cpp
)
cotire(runNLSATTests)
target_link_libraries(runNLSATTests libboost_unit_test_framework.a lib_${PROJECT_NAME} ${libraries})

add_test( NAME nlsat COMMAND runNLSATTests )
