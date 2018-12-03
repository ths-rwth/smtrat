#include <boost/test/unit_test.hpp>

#include <smtrat-common/settings/SettingsParser.h>

BOOST_AUTO_TEST_SUITE(Test_Settings);

BOOST_AUTO_TEST_CASE(parse)
{
	auto& sp = smtrat::SettingsParser::getInstance();
	
	std::cout << sp.print_help() << std::endl;

	sp.parse_options(
		boost::unit_test::framework::master_test_suite().argc,
		boost::unit_test::framework::master_test_suite().argv
	);

	std::cout << sp.print_options() << std::endl;
	std::cout << sp.print_help() << std::endl;
}

BOOST_AUTO_TEST_SUITE_END();