#define BOOST_TEST_MODULE test_mcsatvs
//#include <boost/test/included/unit_test.hpp>
#include <boost/test/unit_test.hpp>

#include <smtrat-common/smtrat-common.h>

struct MCSATVSFixture {
	MCSATVSFixture() {
		// std::cout << "Fixture" << std::endl;
		if (!carl::logging::logger().has("stdout")) {
			carl::logging::logger().configure("stdout", std::cout);
		}
		carl::logging::logger().formatter("stdout")->printInformation = true;
		carl::logging::logger().filter("stdout")
			("smtrat.mcsat.vs", carl::logging::LogLevel::LVL_DEBUG)
			("smtrat.test.mcsatvs", carl::logging::LogLevel::LVL_DEBUG)
		;
	}
};

BOOST_GLOBAL_FIXTURE( MCSATVSFixture );
