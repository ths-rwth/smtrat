/*
 * File:   ConstraintMatrixFactory_unittest.h
 * Author: square
 *
 * Created on May 10, 2012, 3:13 PM
 */

#ifndef CONSTRAINTMATRIXFACTORY_UNITTEST_H
#define CONSTRAINTMATRIXFACTORY_UNITTEST_H

#include <cppunit/extensions/HelperMacros.h>

class ConstraintMatrixFactory_unittest:
    public CPPUNIT_NS:: TestFixture
{
    CPPUNIT_TEST_SUITE( ConstraintMatrixFactory_unittest );
    CPPUNIT_TEST( testMethod );

 CPPUNIT_TEST_SUITE_END()

 ;

 public:
     ConstraintMatrixFactory_unittest();
     virtual ~ConstraintMatrixFactory_unittest();
     void setUp();
     void tearDown();

 private:

     void testMethod();

};

#endif   /* CONSTRAINTMATRIXFACTORY_UNITTEST_H */
