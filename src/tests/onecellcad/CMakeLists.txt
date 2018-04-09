add_executable(runOpenCellCadTests
  Test_OpenCad.cpp
)

target_link_libraries(runOpenCellCadTests
  libboost_unit_test_framework.a
  lib_${PROJECT_NAME}
  ${libraries}
)

add_executable(runOneCellCadTests
  Test_OneCellCAD.cpp
)

target_link_libraries(runOneCellCadTests
  libboost_unit_test_framework.a
  lib_${PROJECT_NAME}
  ${libraries}
)
