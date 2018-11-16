add_executable( runFourierMotzkinQETests
	Test_fmqe.cpp
)
cotire(runFourierMotzkinQETests)
target_link_libraries(runFourierMotzkinQETests
    ${Boost_UNIT_TEST_FRAMEWORK_LIBRARY}
    lib_${PROJECT_NAME}
    ${libraries})

add_test( NAME FourierMotzkinQE COMMAND runFourierMotzkinQETests )
