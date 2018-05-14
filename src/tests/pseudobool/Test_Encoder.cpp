#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE test_PseudoBool
#include <boost/test/unit_test.hpp>

#include "../../lib/Common.h"

struct PseudoBoolFixture {
	PseudoBoolFixture() {
		std::cout << "Fixture" << std::endl;
		if (!carl::logging::logger().has("stdout")) {
			carl::logging::logger().configure("stdout", std::cout);
		}
		carl::logging::logger().formatter("stdout")->printInformation = false;
		carl::logging::logger().filter("stdout")
			("smtrat.pbc", carl::logging::LogLevel::LVL_DEBUG)
		;
	}
};

BOOST_GLOBAL_FIXTURE( PseudoBoolFixture );
