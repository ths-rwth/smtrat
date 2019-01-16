#define BOOST_TEST_MODULE test_nlsat
#include <boost/test/unit_test.hpp>

#include <smtrat-common/smtrat-common.h>

struct NLSATFixture {
	NLSATFixture() {
		std::cout << "Fixture" << std::endl;
		if (!carl::logging::logger().has("stdout")) {
			carl::logging::logger().configure("stdout", std::cout);
		}
		carl::logging::logger().formatter("stdout")->printInformation = true;
		carl::logging::logger().filter("stdout")
			("smtrat.nlsat", carl::logging::LogLevel::LVL_DEBUG)
			("smtrat.test.nlsat", carl::logging::LogLevel::LVL_DEBUG)
		;
	}
};

BOOST_GLOBAL_FIXTURE( NLSATFixture );
