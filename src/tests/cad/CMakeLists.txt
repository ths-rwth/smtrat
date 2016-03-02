add_executable( runCADTests
	Test_CAD.cpp
	Test_Projection.cpp
)
cotire(runCADTests)
target_link_libraries(runCADTests libboost_unit_test_framework.a lib_${PROJECT_NAME} ${libraries})

add_test( NAME cad COMMAND runCADTests )
