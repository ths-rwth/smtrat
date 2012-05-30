/*
 * File:   GroebnerToSDP_unittest.cpp
 * Author: square
 *
 * Created on May 10, 2012, 2:41 PM
 */

#include "GroebnerToSDP_unittest.h"
#include "ginacra/settings.h"

#include "smtrat.h"
#include "ginacra/VariableListPool.h"
#include "ginacra/mr/Buchberger.h"
#include "../modules/NSSModule/GroebnerToSDP.h"

using namespace smtrat;
using namespace GiNaCRA;

using GiNaC::symbol;

CPPUNIT_TEST_SUITE_REGISTRATION( GroebnerToSDP_unittest );

GroebnerToSDP_unittest::GroebnerToSDP_unittest(){}

GroebnerToSDP_unittest::~GroebnerToSDP_unittest(){}

void GroebnerToSDP_unittest::setUp(){}

void GroebnerToSDP_unittest::tearDown(){}

void GroebnerToSDP_unittest::testIterator()
{
    MonomialIterator mit( 4 );
    //std::cout << "4.3" << std::endl;
    //mit.test(3);

    MonomialIterator mit2( 3 );
    //std::cout << "3.3" << std::endl;
    //mit2.test(3);

}

void GroebnerToSDP_unittest::testMethod()
{
    GiNaCRA::MultivariatePolynomialSettings::InitializeGiNaCRAMultivariateMR();
    VariableListPool::ensureNrVariables( 6 );

    symbol a = VariableListPool::getVariableSymbol( 0 );
    symbol b = VariableListPool::getVariableSymbol( 1 );
    symbol c = VariableListPool::getVariableSymbol( 2 );
    symbol x = VariableListPool::getVariableSymbol( 3 );
    symbol y = VariableListPool::getVariableSymbol( 4 );
    symbol z = VariableListPool::getVariableSymbol( 5 );

    //{a2 − x + y, b2 − z, xzc2 − yzc2 + 1
    MultivariatePolynomialMR<Lexicographic> g1 = MultivariatePolynomialMR<Lexicographic>( a * a - x + y );
    MultivariatePolynomialMR<Lexicographic> g2 = MultivariatePolynomialMR<Lexicographic>( b * b - z );
    MultivariatePolynomialMR<Lexicographic> g3 = MultivariatePolynomialMR<Lexicographic>( x * z * c * c - y * z * c * c + 1 );

    MultivariateIdeal<Lexicographic>        id1;
    id1.addGenerator( g1 );
    id1.addGenerator( g2 );
    id1.addGenerator( g3 );

    GroebnerToSDP<Lexicographic> gsdp( id1, MonomialIterator( 6 ) );

    std::cout << gsdp.findWitness();

}
