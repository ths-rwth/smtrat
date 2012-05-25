/* 
 * File:   DenseMatrix_unittest.cpp
 * Author: square
 * 
 * Created on May 14, 2012, 8:13 PM
 */

#include "DenseMatrix_unittest.h"
#include "../utilities/LinAlg/DenseMatrix.h"
#include "modules/NSSModule/ConstraintMatrixFactory.h"

using namespace smtrat;

CPPUNIT_TEST_SUITE_REGISTRATION(DenseMatrix_unittest);

DenseMatrix_unittest::DenseMatrix_unittest() {
}

DenseMatrix_unittest::~DenseMatrix_unittest() {
}

void DenseMatrix_unittest::setUp() {
	
}

void DenseMatrix_unittest::tearDown() {
	
}

void DenseMatrix_unittest::testMethod() {
	DenseMatrix mM(3,3);
	Rational* row = new Rational[3];
	row[0] = 1;
	row[1] = 2;
	row[2] = 3;
	mM.writeRow(row, 0);
	
	mM.set(1,1,5);
	CPPUNIT_ASSERT_EQUAL(Rational(1),mM.get(0,0));
	CPPUNIT_ASSERT_EQUAL(Rational(5),mM.get(1,1));
}

void DenseMatrix_unittest::testSwap() {
	
	DenseMatrix mM(3,3);
	Rational* row = new Rational[3];
	row[0] = 1;
	row[1] = 2;
	row[2] = 3;
	mM.writeRow(row, 0);
	mM.swapRow(0,2);
	CPPUNIT_ASSERT_EQUAL(Rational(2), mM.get(2,1));
	CPPUNIT_ASSERT_EQUAL(Rational(0), mM.get(0,1));
}

void DenseMatrix_unittest::testEchelon() {
	DenseMatrix A(3,4);
	A.set(0,0,-2);
	A.set(0,1,-4 );
	A.set(0,2, 0);
	A.set(0,3, -10);
	A.set(1,0, 2);
	A.set(1,1, 1);
	A.set(1,2, 6);
	A.set(1,3, 22);
	A.set(2,0, -2);
	A.set(2,1, -2);
	A.set(2,2, 0);
	A.set(2,3, -6);
	//A.print();
	A.rowEchelon();
	//A.print();
	CPPUNIT_ASSERT_EQUAL(Rational(-2), A.get(0,0));
	CPPUNIT_ASSERT_EQUAL(Rational(0), A.get(1,0));
	CPPUNIT_ASSERT_EQUAL(Rational(-3), A.get(1,1));
	CPPUNIT_ASSERT_EQUAL(Rational(6), A.get(1,2));
	CPPUNIT_ASSERT_EQUAL(Rational(12), A.get(1,3));
	
}

void DenseMatrix_unittest::testSolve() {
	std::vector<Rational> approx(3, Rational(0));
	approx[0] = "2/3";
	approx[1] = 2;
	approx[2] = "14/5";
	
	
	DenseMatrix A(3,4);
	A.set(0,0,-2);
	A.set(0,1,-4 );
	A.set(0,2, 0);
	A.set(0,3, -10);
	A.set(1,0, 2);
	A.set(1,1, 1);
	A.set(1,2, 6);
	A.set(1,3, 22);
	A.set(2,0, -2);
	A.set(2,1, -2);
	A.set(2,2, 0);
	A.set(2,3, -6);
	//A.print();
	A.rowEchelon();
	std::vector<Rational> sol = A.SolveExactSolution(approx);
	CPPUNIT_ASSERT_EQUAL(Rational(1), sol[0]);
	CPPUNIT_ASSERT_EQUAL(Rational(2), sol[1]);
	CPPUNIT_ASSERT_EQUAL(Rational(3), sol[2]);
	
	
}

void DenseMatrix_unittest::testColOrder() {
	DenseMatrix A(3,4);
	A.set(0,0, 10);
	A.set(1,0, 11);
	A.set(2,0, 12);
	A.set(1,1, 2);
	A.set(2,2, 3);
	A.set(0,3, 40);
	A.set(1,3, 41);
	A.set(2,3, 42);
	std::vector<size_t> cO;
	cO.push_back(1);
	cO.push_back(0);
	cO.push_back(3);
	cO.push_back(2);
	//A.print();
	A.permuteColumns(cO);
	//A.print();
	CPPUNIT_ASSERT_EQUAL(Rational(11), A.get(1,1));
	CPPUNIT_ASSERT_EQUAL(Rational(10), A.get(0,1));
	CPPUNIT_ASSERT_EQUAL(Rational(3), A.get(2,3));
	A.unpermuteColumns(cO);
	CPPUNIT_ASSERT_EQUAL(Rational(2), A.get(1,1));
	CPPUNIT_ASSERT_EQUAL(Rational(42), A.get(2,3));
	
}