add_executable( runFourierMotzkinQETests
	Test_fmqe.cpp
)
cotire(runFourierMotzkinQETests)
target_link_libraries(runFourierMotzkinQETests
	Boost_unit_test_framework_SHARED
	smtrat-qe-shared
)

add_test( NAME FourierMotzkinQE COMMAND runFourierMotzkinQETests )
