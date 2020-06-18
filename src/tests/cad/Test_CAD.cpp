#define BOOST_TEST_MODULE test_cad
#include <boost/test/unit_test.hpp>

#include <smtrat-common/smtrat-common.h>
#include <carl-logging/logging-internals.h>

struct CADFixture {
	CADFixture() {
		std::cout << "Fixture" << std::endl;
		if (!carl::logging::logger().has("stdout")) {
			carl::logging::logger().configure("stdout", std::cout);
		}
		carl::logging::logger().formatter("stdout")->printInformation = false;
		carl::logging::logger().filter("stdout")
			("smtrat.cad", carl::logging::LogLevel::LVL_DEBUG)
		;
	}
};

BOOST_GLOBAL_FIXTURE( CADFixture );
