/*
 * File:   DenseMatrix_unittest.h
 * Author: square
 *
 * Created on May 14, 2012, 8:13 PM
 */

#ifndef DENSEMATRIX_UNITTEST_H
#define DENSEMATRIX_UNITTEST_H

#include <cppunit/extensions/HelperMacros.h>
#include "../utilities/LinAlg/DenseMatrix.h"

class DenseMatrix_unittest:
    public CPPUNIT_NS:: TestFixture
{
    CPPUNIT_TEST_SUITE( DenseMatrix_unittest );
    CPPUNIT_TEST( testMethod );
    CPPUNIT_TEST( testSwap );
    CPPUNIT_TEST( testEchelon );
    CPPUNIT_TEST( testSolve );
    CPPUNIT_TEST( testColOrder );

 CPPUNIT_TEST_SUITE_END()

 ;

 public:
     DenseMatrix_unittest();
     virtual ~DenseMatrix_unittest();
     void setUp();
     void tearDown();

 private:
     //  smtrat::DenseMatrix mM;
     void testMethod();
     void testSwap();
     void testEchelon();
     void testSolve();
     void testColOrder();

};

#endif   /* DENSEMATRIX_UNITTEST_H */
