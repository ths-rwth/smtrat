/**
 * Entry point for unittests.
 * @file   test.cpp
 * @author Sebastian Junges
 *
 * @version 2012-04-03
 */

#include <iostream>
#include <cppunit/CompilerOutputter.h>
#include <cppunit/extensions/TestFactoryRegistry.h>
#include <cppunit/ui/text/TestRunner.h>

int main( int argc, char** argv )
{
    // Get the top level suite from the registry
    CppUnit::Test*              test_all = CppUnit::TestFactoryRegistry::getRegistry().makeTest();
    CppUnit::TextUi::TestRunner runner;
    runner.addTest( test_all );

    // Change the default outputter to a compiler error format outputter
    runner.setOutputter( new CppUnit::CompilerOutputter( &runner.result(), std::cerr ) );

    // Run the tests. Return 1 if a test didnt pass.
    return !runner.run();

}
