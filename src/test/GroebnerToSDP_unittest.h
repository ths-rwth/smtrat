/*
 * File:   GroebnerToSDP_unittest.h
 * Author: square
 *
 * Created on May 10, 2012, 2:41 PM
 */

#ifndef GROEBNERTOSDP_UNITTEST_H
#define GROEBNERTOSDP_UNITTEST_H

#include <cppunit/extensions/HelperMacros.h>

class GroebnerToSDP_unittest:
    public CPPUNIT_NS:: TestFixture
{
    CPPUNIT_TEST_SUITE( GroebnerToSDP_unittest );
    CPPUNIT_TEST( testMethod );
    CPPUNIT_TEST( testIterator );

 CPPUNIT_TEST_SUITE_END()

 ;

 public:
     GroebnerToSDP_unittest();
     virtual ~GroebnerToSDP_unittest();
     void setUp();
     void tearDown();

 private:
     void testIterator();
     void testMethod();

};

#endif   /* GROEBNERTOSDP_UNITTEST_H */
