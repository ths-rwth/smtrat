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

#include "../VSModule/SqrtEx.h"
#include "../../Formula.h"
#include <cmath>

namespace svs
{
    /*
     * Methods:
     */
    smtrat::Formula* substituteNormal( const smtrat::Constraint*, const GiNaC::symbol&, const vs::SqrtEx& );
    smtrat::Formula* substituteNormalSqrtEq( const GiNaC::ex&, const GiNaC::ex&, const GiNaC::ex& );
    smtrat::Formula* substituteNormalSqrtNeq( const GiNaC::ex&, const GiNaC::ex&, const GiNaC::ex& );
    smtrat::Formula* substituteNormalSqrtLess( const GiNaC::ex&, const GiNaC::ex&, const GiNaC::ex&, const GiNaC::ex& );
    smtrat::Formula* substituteNormalSqrtLeq( const GiNaC::ex&, const GiNaC::ex&, const GiNaC::ex&, const GiNaC::ex& );
    smtrat::Formula* substitutePlusEps( const smtrat::Constraint*, const GiNaC::symbol&, const vs::SqrtEx& );
    smtrat::Formula* substituteEpsGradients( const smtrat::Constraint*, const GiNaC::symbol&, const vs::SqrtEx&, const smtrat::Constraint_Relation, const smtrat::Constraint_Relation );
    smtrat::Formula* substituteMinusInf( const smtrat::Constraint*, const GiNaC::symbol&, const vs::SqrtEx& );
    smtrat::Formula* substituteInfLessGreater( const smtrat::Constraint&, const GiNaC::symbol&, const vs::SqrtEx& );
    smtrat::Formula* substituteTrivialCase( const smtrat::Constraint&, const GiNaC::symbol&, const vs::SqrtEx& );
    smtrat::Formula* substituteNotTrivialCase( const smtrat::Constraint&, const GiNaC::symbol&, const vs::SqrtEx& );
#ifdef VS_CUBIC_CASE
    void substituteCubicRoot( const smtrat::Constraint&, const Substitution&, DisjunctionOfConstraintConjunctions& );
    void substituteCubicRootInLinear( const smtrat::Constraint&,
                                      const Substitution&,
                                      const GiNaC::ex&,
                                      const GiNaC::ex&,
                                      DisjunctionOfConstraintConjunctions&,
                                      const GiNaC::ex&,
                                      const GiNaC::symtab& );
    void substituteCubicRootInQuadratic( const smtrat::Constraint&,
                                         const Substitution&,
                                         const GiNaC::ex&,
                                         const GiNaC::ex&,
                                         DisjunctionOfConstraintConjunctions&,
                                         const GiNaC::ex&,
                                         const GiNaC::symtab& );
    void substituteSingleCubicRootInQuadraticGreaterZero( const GiNaC::ex&,
                                                          const Substitution&,
                                                          const Substitution&,
                                                          DisjunctionOfConstraintConjunctions&,
                                                          const GiNaC::symtab& );
    void substituteSingleCubicRootInQuadraticLessZero( const GiNaC::ex&,
                                                       const Substitution&,
                                                       const Substitution&,
                                                       DisjunctionOfConstraintConjunctions&,
                                                       const GiNaC::symtab& );
    void substituteTripleCubicRootInLinear( const GiNaC::ex&,
                                            const GiNaC::ex&,
                                            const bool,
                                            const Substitution&,
                                            const Substitution&,
                                            const Substitution&,
                                            DisjunctionOfConstraintConjunctions&,
                                            const GiNaC::symtab& );
    void substituteTripleCubicRootInQuadratic( const GiNaC::ex&,
                                               const GiNaC::ex&,
                                               const bool,
                                               const Substitution&,
                                               const Substitution&,
                                               const Substitution&,
                                               const Substitution&,
                                               DisjunctionOfConstraintConjunctions&,
                                               const GiNaC::symtab& );
#endif

}    // end namspace vs

#endif
