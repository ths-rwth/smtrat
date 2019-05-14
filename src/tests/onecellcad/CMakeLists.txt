# TODO test not compiling, enable when fixed
add_executable(runOpenCellCadTests
   Test_OpenCad.cpp
)
target_link_libraries(runOpenCellCadTests
	${Boost_unit_test_framework_SHARED}
	smtrat-mcsat-shared
)

# TODO test not compiling, enable when fixed
add_executable(runOneCellCadTests
  Test_OneCellCAD.cpp
)
target_link_libraries(runOneCellCadTests
	${Boost_unit_test_framework_SHARED}
	smtrat-mcsat-shared
)


add_executable(runOneCellCadBugTests
  Test_OneCellCADBug.cpp
)
target_link_libraries(runOneCellCadBugTests
  ${Boost_unit_test_framework_SHARED}
  lib_${PROJECT_NAME}
  smtrat-mcsat-shared
  ${libraries}
)
add_test(NAME onecellcadbug COMMAND runOneCellCadBugTests)
