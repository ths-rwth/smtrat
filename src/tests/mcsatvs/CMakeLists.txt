file(GLOB_RECURSE test_sources "*.cpp")
add_executable(runMcsatVSTests ${test_sources})

#set(UNITTEST_LIB "${carl_DIR}/resources/lib/libboost_unit_test_framework.a")
#MESSAGE( STATUS "UNITTEST_LIB:         " ${UNITTEST_LIB} )
#target_link_libraries(runMcsatVSTests ${UNITTEST_LIB} lib_${PROJECT_NAME} ${libraries})

target_link_libraries(runMcsatVSTests
	Boost_unit_test_framework_SHARED
	smtrat-mcsat-shared
)
add_test(NAME mcsatvs COMMAND runMcsatVSTests)



#add_executable(runMcsatVSBug
#  Test_McsatVSBug.cpp
#)
#target_link_libraries(runMcsatVSBug
#	Boost_unit_test_framework_SHARED
#	smtrat-mcsat-shared
#	${libraries}
#)
#add_test(NAME mcsatvsbug COMMAND runMcsatVSBug)
