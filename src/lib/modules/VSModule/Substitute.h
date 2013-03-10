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
 * Class containing a method applying a virtual substitution.
 * @author Florian Corzilius
 * @since 2011-05-23
 * @version 2011-12-05
 */

#ifndef SMTRAT_VS_SUBSTITUTE_H
#define SMTRAT_VS_SUBSTITUTE_H

#include "Substitution.h"
#include "Tools.h"
#include <cmath>
#include <bitset>

const unsigned MAX_PRODUCT_SPLIT_NUMBER = 64;

namespace vs
{
    /*
     *  Type and object definitions:
     */

    #ifndef TS_CONSTRAINT_CONJUNCTION
    #define TS_CONSTRAINT_CONJUNCTION
    typedef std::vector<const smtrat::Constraint*> TS_ConstraintConjunction;
    #endif
    typedef std::vector<TS_ConstraintConjunction> DisjunctionOfConstraintConjunctions;

    /*
     * Methods:
     */

    void substitute( const smtrat::Constraint*, const Substitution&, DisjunctionOfConstraintConjunctions& );
    void substituteNormal( const smtrat::Constraint*, const Substitution&, DisjunctionOfConstraintConjunctions& );
    void substituteNormalSqrt( const smtrat::Constraint*, const Substitution&, const GiNaC::ex&, DisjunctionOfConstraintConjunctions& );
    void substituteNormalSqrtEq( const smtrat::Constraint*,
                                 const Substitution&,
                                 const GiNaC::ex&,
                                 const GiNaC::ex&,
                                 const GiNaC::ex&,
                                 const GiNaC::symtab&,
                                 DisjunctionOfConstraintConjunctions& );
    void substituteNormalSqrtNeq( const smtrat::Constraint*,
                                  const Substitution&,
                                  const GiNaC::ex&,
                                  const GiNaC::ex&,
                                  const GiNaC::ex&,
                                 const GiNaC::symtab&,
                                  DisjunctionOfConstraintConjunctions& );
    void substituteNormalSqrtLess( const smtrat::Constraint*,
                                   const Substitution&,
                                   const GiNaC::ex&,
                                   const GiNaC::ex&,
                                   const GiNaC::ex&,
                                   const GiNaC::ex&,
                                 const GiNaC::symtab&,
                                   DisjunctionOfConstraintConjunctions& );
    void substituteNormalSqrtLeq( const smtrat::Constraint*,
                                  const Substitution&,
                                  const GiNaC::ex&,
                                  const GiNaC::ex&,
                                  const GiNaC::ex&,
                                  const GiNaC::ex&,
                                 const GiNaC::symtab&,
                                  DisjunctionOfConstraintConjunctions& );
    void substitutePlusEps( const smtrat::Constraint*, const Substitution&, DisjunctionOfConstraintConjunctions& );
    void substituteEpsGradients( const smtrat::Constraint*,
                                 const Substitution&,
                                 const smtrat::Constraint_Relation,
                                 DisjunctionOfConstraintConjunctions& );
    void substituteMinusInf( const smtrat::Constraint*, const Substitution&, DisjunctionOfConstraintConjunctions& );
    void substituteInfLessGreater( const smtrat::Constraint*, const Substitution&, DisjunctionOfConstraintConjunctions& );
    void substituteTrivialCase( const smtrat::Constraint*, const Substitution&, DisjunctionOfConstraintConjunctions& );
    void substituteNotTrivialCase( const smtrat::Constraint*, const Substitution&, DisjunctionOfConstraintConjunctions& );
    void simplify( DisjunctionOfConstraintConjunctions& );
    void splitProducts( DisjunctionOfConstraintConjunctions& );
    DisjunctionOfConstraintConjunctions splitProducts( const TS_ConstraintConjunction& );
    DisjunctionOfConstraintConjunctions getSignCombinations( const smtrat::Constraint* );
    void getOddBitStrings( unsigned, std::vector< std::bitset<MAX_PRODUCT_SPLIT_NUMBER> >&, unsigned = 0 );
    void getEvenBitStrings( unsigned, std::vector< std::bitset<MAX_PRODUCT_SPLIT_NUMBER> >&, unsigned = 0 );
    GiNaC::ex simplify( const GiNaC::ex&, const GiNaC::symtab&  );
    void print( DisjunctionOfConstraintConjunctions& );
}    // end namspace vs

#endif
