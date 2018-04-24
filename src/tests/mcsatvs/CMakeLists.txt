file(GLOB_RECURSE test_sources "*.cpp")
add_executable(runMcsatVSTests ${test_sources})

# use boost unit test library version from carl

#find_library(UNITTEST_LIB
#    NAMES libboost_unit_test_framework.a libboost_unit_test_framework
#    HINTS "${carl_DIR}/resources/lib"
#)
set(UNITTEST_LIB "${carl_DIR}/resources/lib/libboost_unit_test_framework.a")

#MESSAGE( STATUS "UNITTEST_LIB:         " ${UNITTEST_LIB} )
target_link_libraries(runMcsatVSTests ${UNITTEST_LIB} lib_${PROJECT_NAME} ${libraries})

#target_link_libraries(runMcsatVSTests libboost_unit_test_framework.a lib_${PROJECT_NAME} ${libraries})

add_test(NAME mcsatvs COMMAND runMcsatVSTests)
