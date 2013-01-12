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


/*
 * File:   Condition.h
 * @author Florian Corzilius
 *
 * Created on 11 June 2012, 13:24
 */

#ifndef CONDITION_H
#define CONDITION_H

#include <bitset>
#include <assert.h>
#include <stdio.h>
#include <iostream>

static const unsigned CONDITION_SIZE = 64;

namespace smtrat
{
    class Condition:
        public std::bitset<CONDITION_SIZE>
    {
        public:
            Condition():
                std::bitset<CONDITION_SIZE>()
            {}
            ;
            Condition( const std::bitset<CONDITION_SIZE>& _bisset ):
                std::bitset<CONDITION_SIZE>( _bisset )
            {}
            ;
            Condition( unsigned i ):
                std::bitset<CONDITION_SIZE>()
            {
                assert( i < CONDITION_SIZE );
                (*this)[i] = 1;
            }
            ;

            /**
             * Check whether the bits of this condition are always set if the corresponding bit
             * of the given condition is set.
             *
             * @param _condition The condition to compare with.
             * @return  true,   if all bits of this condition are always set if the corresponding bit
             *                  of the given condition is set;
             *          false,  otherwise.
             */
            bool operator <=( const Condition& _condition ) const
            {
                return (*this & (~_condition)).none();
            }

            // Equivalence
            inline Condition
            operator%( const Condition& _y ) const
            {
              Condition result(~*this);
              result |= _y;
              return result;
            }

            // Implication
            inline Condition
            operator-( const Condition& _y ) const
            {
              Condition result(~*this);
              result ^= _y;
              return result;
            }

            // Xor
            inline Condition
            operator+( const Condition& _y ) const
            {
              Condition result(*this);
              result ^= _y;
              return result;
            }
    };

    static const Condition PROP_TRUE = Condition();

    //Propositions which hold, if they hold for each sub formula of a formula including itself (0-15)
    static const Condition PROP_IS_IN_NNF                       = Condition( 0 );
    static const Condition PROP_IS_IN_CNF                       = Condition( 1 );
    static const Condition PROP_IS_PURE_CONJUNCTION             = Condition( 2 );
    static const Condition PROP_IS_A_CLAUSE                     = Condition( 3 );
    static const Condition PROP_IS_A_LITERAL                    = Condition( 4 );
    static const Condition PROP_IS_AN_ATOM                      = Condition( 5 );
    static const Condition PROP_VARIABLE_DEGREE_LESS_THAN_FIVE  = Condition( 6 );
    static const Condition PROP_VARIABLE_DEGREE_LESS_THAN_FOUR  = Condition( 7 );
    static const Condition PROP_VARIABLE_DEGREE_LESS_THAN_THREE = Condition( 8 );
    static const Condition STRONG_CONDITIONS                    = PROP_IS_IN_NNF | PROP_IS_IN_CNF | PROP_IS_PURE_CONJUNCTION |
                                                                  PROP_IS_A_CLAUSE | PROP_IS_A_LITERAL | PROP_IS_AN_ATOM |
                                                                  PROP_VARIABLE_DEGREE_LESS_THAN_THREE |
                                                                  PROP_VARIABLE_DEGREE_LESS_THAN_FOUR |
                                                                  PROP_VARIABLE_DEGREE_LESS_THAN_THREE;

    //Propositions which hold, if they hold in at least one sub formula (16-31)
    static const Condition PROP_CONTAINS_EQUATION                = Condition( 16 );
    static const Condition PROP_CONTAINS_INEQUALITY              = Condition( 17 );
    static const Condition PROP_CONTAINS_STRICT_INEQUALITY       = Condition( 18 );
    static const Condition PROP_CONTAINS_LINEAR_POLYNOMIAL       = Condition( 19 );
    static const Condition PROP_CONTAINS_NONLINEAR_POLYNOMIAL    = Condition( 20 );
    static const Condition PROP_CONTAINS_MULTIVARIATE_POLYNOMIAL = Condition( 21 );
    static const Condition PROP_CONTAINS_BOOLEAN                 = Condition( 22 );
    static const Condition WEAK_CONDITIONS                       = PROP_CONTAINS_EQUATION | PROP_CONTAINS_INEQUALITY | PROP_CONTAINS_STRICT_INEQUALITY
                                             | PROP_CONTAINS_LINEAR_POLYNOMIAL | PROP_CONTAINS_LINEAR_POLYNOMIAL | PROP_CONTAINS_NONLINEAR_POLYNOMIAL
                                             | PROP_CONTAINS_MULTIVARIATE_POLYNOMIAL | PROP_CONTAINS_INEQUALITY | PROP_CONTAINS_BOOLEAN;

    //Propositions indicating that a solver cannot solve the formula
    static const Condition PROP_CANNOT_BE_SOLVED_BY_SMARTSIMPLIFIER     = Condition( 48 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_GROEBNERMODULE      = Condition( 49 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_VSMODULE            = Condition( 50 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_UNIVARIATECADMODULE = Condition( 51 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_CADMODULE           = Condition( 52 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_SATMODULE           = Condition( 53 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_LRAMODULE           = Condition( 54 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_PREPROMODULE        = Condition( 55 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_PREPROCNFMODULE     = Condition( 57 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_CNFERMODULE         = Condition( 56 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_SINGLEVSMODULE      = Condition( 59 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_ICPMODULE           = Condition( 60 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_ILRAMODULE          = Condition( 61 );
    static const Condition PROP_CANNOT_BE_SOLVED_BY_TLRAMODULE          = Condition( 62 );
    static const Condition SOLVABLE_CONDITIONS                          = PROP_CANNOT_BE_SOLVED_BY_SMARTSIMPLIFIER | PROP_CANNOT_BE_SOLVED_BY_GROEBNERMODULE
                                                 | PROP_CANNOT_BE_SOLVED_BY_VSMODULE | PROP_CANNOT_BE_SOLVED_BY_UNIVARIATECADMODULE
                                                 | PROP_CANNOT_BE_SOLVED_BY_CADMODULE | PROP_CANNOT_BE_SOLVED_BY_SATMODULE
                                                 | PROP_CANNOT_BE_SOLVED_BY_LRAMODULE | PROP_CANNOT_BE_SOLVED_BY_PREPROMODULE
                                                 | PROP_CANNOT_BE_SOLVED_BY_PREPROCNFMODULE | PROP_CANNOT_BE_SOLVED_BY_CNFERMODULE
                                                 | PROP_CANNOT_BE_SOLVED_BY_SINGLEVSMODULE | PROP_CANNOT_BE_SOLVED_BY_ICPMODULE
                                                 | PROP_CANNOT_BE_SOLVED_BY_ILRAMODULE | PROP_CANNOT_BE_SOLVED_BY_TLRAMODULE;
}     // namespace smtrat

#endif   /* CONDITION_H */
