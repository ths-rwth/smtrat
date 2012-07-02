/*
 * File:   ConstraintMatrixFactory_unittest.cpp
 * Author: square
 *
 * Created on May 10, 2012, 3:13 PM
 */

#include "ConstraintMatrixFactory_unittest.h"

#include "../modules/NSSModule/ConstraintMatrixFactory.h"
#include "ginacra/settings.h"
#include "ginacra/VariableListPool.h"
#include "../utilities/SDP/CSDPFacade.h"
#include "../utilities/LinAlg/FindExactSolution.h"
#include "utilities/LinAlg/Cholesky.h"

using namespace smtrat;
using namespace GiNaCRA;

CPPUNIT_TEST_SUITE_REGISTRATION( ConstraintMatrixFactory_unittest );

ConstraintMatrixFactory_unittest::ConstraintMatrixFactory_unittest(){}

ConstraintMatrixFactory_unittest::~ConstraintMatrixFactory_unittest(){}

void ConstraintMatrixFactory_unittest::setUp(){}

void ConstraintMatrixFactory_unittest::tearDown(){}

void ConstraintMatrixFactory_unittest::testMethod()
{
    // 1 + q1,1 − q3,3 + 2q1,2 x − 2q1,2 y + 2q1,3abc + 2q2,3 abcx − 2q2,3 abcy

    GiNaCRA::MultivariatePolynomialSettings::InitializeGiNaCRAMultivariateMR();
    VariableListPool::ensureNrVariables( 6 );
    symbol a = VariableListPool::getVariableSymbol( 0 );
    symbol b = VariableListPool::getVariableSymbol( 1 );
    symbol c = VariableListPool::getVariableSymbol( 2 );
    symbol x = VariableListPool::getVariableSymbol( 3 );
    symbol y = VariableListPool::getVariableSymbol( 4 );
    symbol z = VariableListPool::getVariableSymbol( 5 );

    ConstraintMatrixFactory fac( 3 );
    fac.addReducedTerm( MatrixIndex( 0, 0 ), 1, MultivariateTermMR() );
    fac.addReducedTerm( MatrixIndex( 2, 2 ), -1, MultivariateTermMR() );
    fac.addReducedTerm( MatrixIndex( 0, 1 ), 2, MultivariateTermMR::FromExpression( x ) );
    //fac.addReducedTerm(MatrixIndex(0,1), -2, MultivariateTermMR::FromExpression(y));
    fac.addReducedTerm( MatrixIndex( 1, 1 ), -2, MultivariateTermMR::FromExpression( z ) );

    fac.addReducedTerm( MatrixIndex( 0, 2 ), 2, MultivariateTermMR::FromExpression( a * b * c ) );
    //fac.addReducedTerm(MatrixIndex(1,2), 2, MultivariateTermMR::FromExpression(a*b*c*x));
    fac.addReducedTerm( MatrixIndex( 1, 2 ), -2, MultivariateTermMR::FromExpression( a * b * c * y ) );

    CSDPFacade csdp = CSDPFacade( 3, fac.exportMatrices() );
    std::unique_ptr<std::vector<double> > solution;
    int                                   result = csdp.callRoutine( solution );

    std::cout << "result=" << result << std::endl;
    CPPUNIT_ASSERT( result == 0 );

    //fac.exportLinEqSys().print();
    //std::cout << "--------------------" << std::endl;
    FindExactSolution fes( *solution, fac.exportLinEqSys(), 0.01 );
    //fes.print();
    DenseMatrix sol = fes.getSolutionMatrix( 3 );
    Cholesky chol( sol );
    CPPUNIT_ASSERT( chol.Solve() );

	
	ConstraintMatrixFactory  fact(2);
	
}
