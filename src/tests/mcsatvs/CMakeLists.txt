file(GLOB_RECURSE test_sources "*.cpp")
add_executable(runMcsatVSTests ${test_sources})

#set(UNITTEST_LIB "${carl_DIR}/resources/lib/libboost_unit_test_framework.a")
#MESSAGE( STATUS "UNITTEST_LIB:         " ${UNITTEST_LIB} )
#target_link_libraries(runMcsatVSTests ${UNITTEST_LIB} lib_${PROJECT_NAME} ${libraries})

target_link_libraries(runMcsatVSTests
    ${Boost_unit_test_framework_SHARED}
	lib_${PROJECT_NAME}
	smtrat-mcsat-shared
    ${libraries}
)
add_test(NAME mcsatvs COMMAND runMcsatVSTests)
