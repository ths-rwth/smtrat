file(GLOB_RECURSE test_sources "*.cpp")
add_executable(runOneCellCadTests
  ${test_sources}
)

target_link_libraries(runOneCellCadTests
  libboost_unit_test_framework.a
  lib_${PROJECT_NAME}
  ${libraries}
)

add_test(NAME onecell COMMAND runOneCellCadTests)
