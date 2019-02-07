#include <boost/test/unit_test.hpp>

#include <iostream>

#include <smtrat-cad/CAD.h>

using namespace smtrat;
using namespace smtrat::cad;

BOOST_AUTO_TEST_SUITE(Test_Information);

template<typename T>
void printSize(const std::string& desc) {
	std::cout << "sizeof(" << desc << ") = " << sizeof(T) << std::endl;
}

BOOST_AUTO_TEST_CASE(Test_Info)
{
	printSize<carl::Bitset::BaseType>("Bitset::BaseType");
	printSize<carl::Bitset>("Bitset");
	printSize<Sample>("Sample");
	printSize<carl::tree<Sample>::Node>("Node");
}

BOOST_AUTO_TEST_SUITE_END();
