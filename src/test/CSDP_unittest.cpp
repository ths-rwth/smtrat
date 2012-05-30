/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */


/**
 * Test of interface to CSDP
 * @file   CSDP_unittest.cpp
 * @author Sebastian Junges
 *
 * @version 2012-04-03
 */

#include "CSDP_unittest.h"

#include <vector>
#include <bits/unique_ptr.h>

using namespace smtrat;

using std::unique_ptr;

CPPUNIT_TEST_SUITE_REGISTRATION( CSDP_unittest );

CSDP_unittest::CSDP_unittest(){}

CSDP_unittest::~CSDP_unittest(){}

void CSDP_unittest::setUp(){}

void CSDP_unittest::tearDown(){}

void CSDP_unittest::testCSDP()
{
    //CSDPFacade::test();
    SparseMatrix s1 = SparseMatrix( 7, 7 );
    s1.set( 0, 0, 3 );
    s1.set( 0, 1, 1 );
    //s1.set(1,0,1);
    s1.set( 1, 1, 3 );
    s1.set( 5, 5, 1 );
    s1.PrintEntries();

    SparseMatrix s2 = SparseMatrix( 7, 7 );
    s2.set( 2, 2, 3 );
    s2.set( 2, 4, 1 );
    //s2.set(4,2,1);
    s2.set( 3, 3, 4 );
    s2.set( 4, 4, 5 );
    s2.set( 6, 6, 1 );
    s2.PrintEntries();

    print_debug( "Building cost", 2 );
    double cost[49] =
    {
        2, 1, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0
    };

    print_debug( "Building constraints", 2 );

    std::vector<SparseMatrix> constraints;
    constraints.push_back( s1 );
    constraints.push_back( s2 );

    print_debug( "Building rhs", 2 );
    double b[2] = { 1, 2 };

    print_debug( "Initializing interface to CSDP", 2 );
    CSDPFacade facade = CSDPFacade( 7, cost, constraints, b );

    print_debug( "Call routine", 2 );
    unique_ptr<std::vector<double> > solution;
    facade.callRoutine( solution );
}
