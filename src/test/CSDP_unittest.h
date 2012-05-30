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
 * @file   CSDP_unittest.h
 * @author Sebastian Junges
 *
 * @version 2012-04-03
 */

#ifndef CSDP_UNITTEST_H
#define CSDP_UNITTEST_H

#include <cppunit/extensions/HelperMacros.h>
#include "../utilities/SDP/CSDPFacade.h"
#include "../utilities/debug/debug.h"

class CSDP_unittest:
    public CPPUNIT_NS:: TestFixture
{
    CPPUNIT_TEST_SUITE( CSDP_unittest );

 //CPPUNIT_TEST(testCSDP);
 CPPUNIT_TEST_SUITE_END()

 ;

 public:
     CSDP_unittest();
     virtual ~CSDP_unittest();
     void setUp();
     void tearDown();

 private:
     void testCSDP();
};

#endif   /* CSDP_UNITTEST_H */
