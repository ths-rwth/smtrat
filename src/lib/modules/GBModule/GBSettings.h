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
 * @file:   GBSettings.h
 * @author: Sebastian Junges
 *
 */

#include <ginacra/MultivariatePolynomialMR.h>
#include "../../config.h"

#ifndef GBSETTINGS_H
#define GBSETTINGS_H

namespace smtrat
{
   /**
     * Only active if we check inequalities.
     * AS_RECEIVED: Do not change the received inequalities.
     * FULL_REDUCED: Pass the fully reduced received inequalities.
     * REDUCED: Pass the reduced received inequalities.
     * REDUCED_ONLYSTRICT: Pass the nonstrict inequalities reduced, the others unchanged
     * FULL_REDUCED_ONLYNEW: Do only a full reduce on the newly added received inequalities.
     */
    enum pass_inequalities { AS_RECEIVED, FULL_REDUCED, FULL_REDUCED_IF };

    enum after_firstInfeasibleSubset { RETURN_DIRECTLY, PROCEED_INFEASIBLEANDDEDUCTION, PROCEED_ALLINEQUALITIES };

    enum theory_deductions { NO_CONSTRAINTS, ONLY_INEQUALITIES, ALL_CONSTRAINTS };

    enum check_inequalities { ALWAYS, AFTER_NEW_GB, NEVER };
	
	enum transform_inequalities { ALL_INEQUALITIES, ONLY_NONSTRICT, NO_INEQUALITIES };
    
    enum backtracking_mode { CHRONOLOGICAL, NON_CHRONOLOGICAL };
	
	
	struct decidePassingPolynomial;

    // Contains a bug, e.g. rect-03-10
    struct GBSettings5
    {
        static const unsigned                            identifier                              = 5;
        
        typedef GiNaCRA::GradedLexicgraphic              Order;
        typedef GiNaCRA::MultivariatePolynomialMR<Order> Polynomial;
        typedef GiNaCRA::MultivariateIdeal<Order>        MultivariateIdeal;
        typedef GiNaCRA::BaseReductor<Order>             Reductor;
		typedef smtrat::decidePassingPolynomial			 passPolynomial;

        static const bool                                passGB                                  = true;
        static const bool                                getReasonsForInfeasibility              = true;
        static const bool                                passWithMinimalReasons                  = true;
        static const check_inequalities                  checkInequalities                       = ALWAYS;
        static const pass_inequalities                   passInequalities                        = FULL_REDUCED;
        static const after_firstInfeasibleSubset         withInfeasibleSubset                    = PROCEED_ALLINEQUALITIES;
        static const theory_deductions                   addTheoryDeductions                     = ALL_CONSTRAINTS;
        static const unsigned                            setCheckInequalitiesToBeginAfter        = 0;
        static const bool                                checkInequalitiesForTrivialSumOfSquares = true;
        static const bool                                checkEqualitiesForTrivialSumOfSquares   = true;
		static const transform_inequalities				 transformIntoEqualities				 = NO_INEQUALITIES;
        
        static const unsigned                            maxSearchExponent                       = 11;

		static const bool								 applyNSS								 = false;
        static const unsigned                            maxSDPdegree                            = 4;
        static const unsigned                            SDPupperBoundNrVariables                = 6;
		static const unsigned							 callSDPAfterNMonomials					 = 6;
		static const unsigned							 sternBrocotStartPrecisionOneTo			 = 80;
		static const unsigned							 sternBrocotHigherPrecisionSteps		 = 2;
		static const unsigned							 sternBrocotHigherPrecisionFactor		 = 10;
    };
    
    // causes a bug to appear (see stats)
    struct GBSettings51
    {
        static const unsigned                            identifier                              = 51;
        
        typedef GiNaCRA::GradedLexicgraphic              Order;
        typedef GiNaCRA::MultivariatePolynomialMR<Order> Polynomial;
        typedef GiNaCRA::MultivariateIdeal<Order>        MultivariateIdeal;
        typedef GiNaCRA::BaseReductor<Order>             Reductor;
		typedef smtrat::decidePassingPolynomial			 passPolynomial;

        static const bool                                passGB                                  = true;
        static const bool                                getReasonsForInfeasibility              = true;
        static const bool                                passWithMinimalReasons                  = true;
        static const check_inequalities                  checkInequalities                       = AFTER_NEW_GB;
        static const pass_inequalities                   passInequalities                        = FULL_REDUCED;
        static const after_firstInfeasibleSubset         withInfeasibleSubset                    = PROCEED_ALLINEQUALITIES;
        static const theory_deductions                   addTheoryDeductions                     = ALL_CONSTRAINTS;
        static const unsigned                            setCheckInequalitiesToBeginAfter        = 0;
        static const bool                                checkInequalitiesForTrivialSumOfSquares = true;
        static const bool                                checkEqualitiesForTrivialSumOfSquares   = true;
		static const transform_inequalities				 transformIntoEqualities				 = NO_INEQUALITIES;

		static const bool								 applyNSS								 = false;
        static const unsigned                            maxSDPdegree                            = 4;
        static const unsigned                            SDPupperBoundNrVariables                = 6;
		static const unsigned							 callSDPAfterNMonomials					 = 6;
		static const unsigned							 sternBrocotStartPrecisionOneTo			 = 80;
		static const unsigned							 sternBrocotHigherPrecisionSteps		 = 2;
		static const unsigned							 sternBrocotHigherPrecisionFactor		 = 10;
    };
    
    struct GBSettings3
    {
        static const unsigned                            identifier                              = 3;
        
        typedef GiNaCRA::GradedLexicgraphic              Order;
        typedef GiNaCRA::MultivariatePolynomialMR<Order> Polynomial;
        typedef GiNaCRA::MultivariateIdeal<Order>        MultivariateIdeal;
        typedef GiNaCRA::BaseReductor<Order>             Reductor;
		typedef smtrat::decidePassingPolynomial			 passPolynomial;

        static const bool                                passGB                                  = true;
        static const bool                                getReasonsForInfeasibility              = true;
        static const bool                                passWithMinimalReasons                  = true;
        static const backtracking_mode                   backtrackingGB                          = CHRONOLOGICAL;
        static const backtracking_mode                   backtrackingIneq                        = CHRONOLOGICAL;
        static const check_inequalities                  checkInequalities                       = ALWAYS;
        static const pass_inequalities                   passInequalities                        = AS_RECEIVED;
        static const after_firstInfeasibleSubset         withInfeasibleSubset                    = PROCEED_INFEASIBLEANDDEDUCTION;
        static const theory_deductions                   addTheoryDeductions                     = NO_CONSTRAINTS;
        static const unsigned                            setCheckInequalitiesToBeginAfter        = 0;
        static const bool                                checkInequalitiesForTrivialSumOfSquares = true;
        static const bool                                checkEqualitiesForTrivialSumOfSquares   = true;
		static const transform_inequalities				 transformIntoEqualities				 = NO_INEQUALITIES;

		static const bool								 applyNSS								 = false;
        static const unsigned                            maxSDPdegree                            = 4;
        static const unsigned                            SDPupperBoundNrVariables                = 6;
		static const unsigned							 callSDPAfterNMonomials					 = 6;
		static const unsigned							 sternBrocotStartPrecisionOneTo			 = 80;
		static const unsigned							 sternBrocotHigherPrecisionSteps		 = 2;
		static const unsigned							 sternBrocotHigherPrecisionFactor		 = 10;
    };
   
    struct GBSettings1
    {
        static const unsigned                            identifier                              = 1;
        
        typedef GiNaCRA::GradedLexicgraphic              Order;
        typedef GiNaCRA::MultivariatePolynomialMR<Order> Polynomial;
        typedef GiNaCRA::MultivariateIdeal<Order>        MultivariateIdeal;
        typedef GiNaCRA::BaseReductor<Order>             Reductor;
		typedef smtrat::decidePassingPolynomial			 passPolynomial;

        static const bool                                passGB                                  = true;
        static const bool                                getReasonsForInfeasibility              = false;
        static const bool                                passWithMinimalReasons                  = false;
        static const check_inequalities                  checkInequalities                       = NEVER;
        static const pass_inequalities                   passInequalities                        = AS_RECEIVED;
        static const after_firstInfeasibleSubset         withInfeasibleSubset                    = PROCEED_INFEASIBLEANDDEDUCTION;
        static const theory_deductions                   addTheoryDeductions                     = ONLY_INEQUALITIES;
        static const unsigned                            setCheckInequalitiesToBeginAfter        = 0;
        static const bool                                checkInequalitiesForTrivialSumOfSquares = true;
        static const bool                                checkEqualitiesForTrivialSumOfSquares   = true;
		static const transform_inequalities				 transformIntoEqualities				 = NO_INEQUALITIES;

		static const bool								 applyNSS								 = false;
        static const unsigned                            maxSDPdegree                            = 4;
        static const unsigned                            SDPupperBoundNrVariables                = 6;
		static const unsigned							 callSDPAfterNMonomials					 = 6;
		static const unsigned							 sternBrocotStartPrecisionOneTo			 = 80;
		static const unsigned							 sternBrocotHigherPrecisionSteps		 = 2;
		static const unsigned							 sternBrocotHigherPrecisionFactor		 = 10;
    };
   
    
 	/**
      struct GBSettings2
    {
        static const unsigned                            identifier                              = 2;
        
        typedef GiNaCRA::GradedLexicgraphic              Order;
        typedef GiNaCRA::MultivariatePolynomialMR<Order> Polynomial;
        typedef GiNaCRA::MultivariateIdeal<Order>        MultivariateIdeal;
        typedef GiNaCRA::BaseReductor<Order>             Reductor;
		typedef smtrat::decidePassingPolynomial			 passPolynomial;

        static const bool                                passGB                                  = true;
        static const bool                                getReasonsForInfeasibility              = true;
        static const bool                                passWithMinimalReasons                  = true;
        static const check_inequalities                  checkInequalities                       = NEVER;
        static const pass_inequalities                   passInequalities                        = AS_RECEIVED;
        static const after_firstInfeasibleSubset         withInfeasibleSubset                    = PROCEED_INFEASIBLEANDDEDUCTION;
        static const theory_deductions                   addTheoryDeductions                     = ONLY_INEQUALITIES;
        static const unsigned                            setCheckInequalitiesToBeginAfter        = 0;
        static const bool                                checkInequalitiesForTrivialSumOfSquares = true;
        static const bool                                checkEqualitiesForTrivialSumOfSquares   = true;
		static const transform_inequalities				 transformIntoEqualities				 = NO_INEQUALITIES;

		static const bool								 applyNSS								 = false;
        static const unsigned                            maxSDPdegree                            = 4;
        static const unsigned                            SDPupperBoundNrVariables                = 6;
		static const unsigned							 callSDPAfterNMonomials					 = 6;
		static const unsigned							 sternBrocotStartPrecisionOneTo			 = 80;
		static const unsigned							 sternBrocotHigherPrecisionSteps		 = 2;
		static const unsigned							 sternBrocotHigherPrecisionFactor		 = 10;
    };
    
      struct GBSettings4
    {
        static const unsigned                            identifier                              = 4;
        
        typedef GiNaCRA::GradedLexicgraphic              Order;
        typedef GiNaCRA::MultivariatePolynomialMR<Order> Polynomial;
        typedef GiNaCRA::MultivariateIdeal<Order>        MultivariateIdeal;
        typedef GiNaCRA::BaseReductor<Order>             Reductor;
		typedef smtrat::decidePassingPolynomial			 passPolynomial;

        static const bool                                passGB                                  = true;
        static const bool                                getReasonsForInfeasibility              = true;
        static const bool                                passWithMinimalReasons                  = true;
        static const check_inequalities                  checkInequalities                       = ALWAYS;
        static const pass_inequalities                   passInequalities                        = FULL_REDUCED;
        static const after_firstInfeasibleSubset         withInfeasibleSubset                    = RETURN_DIRECTLY;
        static const theory_deductions                   addTheoryDeductions                     = NO_CONSTRAINTS;
        static const unsigned                            setCheckInequalitiesToBeginAfter        = 0;
        static const bool                                checkInequalitiesForTrivialSumOfSquares = true;
        static const bool                                checkEqualitiesForTrivialSumOfSquares   = true;
		static const transform_inequalities				 transformIntoEqualities				 = NO_INEQUALITIES;

		static const bool								 applyNSS								 = false;
        static const unsigned                            maxSDPdegree                            = 4;
        static const unsigned                            SDPupperBoundNrVariables                = 6;
		static const unsigned							 callSDPAfterNMonomials					 = 6;
		static const unsigned							 sternBrocotStartPrecisionOneTo			 = 80;
		static const unsigned							 sternBrocotHigherPrecisionSteps		 = 2;
		static const unsigned							 sternBrocotHigherPrecisionFactor		 = 10;
    };
    
    struct GBSettings5
    {
        static const unsigned                            identifier                              = 5;
        
        typedef GiNaCRA::GradedLexicgraphic              Order;
        typedef GiNaCRA::MultivariatePolynomialMR<Order> Polynomial;
        typedef GiNaCRA::MultivariateIdeal<Order>        MultivariateIdeal;
        typedef GiNaCRA::BaseReductor<Order>             Reductor;
		typedef smtrat::decidePassingPolynomial			 passPolynomial;

        static const bool                                passGB                                  = true;
        static const bool                                getReasonsForInfeasibility              = true;
        static const bool                                passWithMinimalReasons                  = true;
        static const check_inequalities                  checkInequalities                       = ALWAYS;
        static const pass_inequalities                   passInequalities                        = FULL_REDUCED;
        static const after_firstInfeasibleSubset         withInfeasibleSubset                    = PROCEED_ALLINEQUALITIES;
        static const theory_deductions                   addTheoryDeductions                     = ALL_CONSTRAINTS;
        static const unsigned                            setCheckInequalitiesToBeginAfter        = 0;
        static const bool                                checkInequalitiesForTrivialSumOfSquares = true;
        static const bool                                checkEqualitiesForTrivialSumOfSquares   = true;
		static const transform_inequalities				 transformIntoEqualities				 = NO_INEQUALITIES;

		static const bool								 applyNSS								 = false;
        static const unsigned                            maxSDPdegree                            = 4;
        static const unsigned                            SDPupperBoundNrVariables                = 6;
		static const unsigned							 callSDPAfterNMonomials					 = 6;
		static const unsigned							 sternBrocotStartPrecisionOneTo			 = 80;
		static const unsigned							 sternBrocotHigherPrecisionSteps		 = 2;
		static const unsigned							 sternBrocotHigherPrecisionFactor		 = 10;
    };
    */
    struct GBSettings6
    {
        static const unsigned                            identifier                              = 6;
        
        typedef GiNaCRA::GradedLexicgraphic              Order;
        typedef GiNaCRA::MultivariatePolynomialMR<Order> Polynomial;
        typedef GiNaCRA::MultivariateIdeal<Order>        MultivariateIdeal;
        typedef GiNaCRA::BaseReductor<Order>             Reductor;
		typedef smtrat::decidePassingPolynomial			 passPolynomial;

        static const bool                                passGB                                  = false;
        static const bool                                getReasonsForInfeasibility              = true;
        static const bool                                passWithMinimalReasons                  = false;
        static const check_inequalities                  checkInequalities                       = NEVER;
        static const pass_inequalities                   passInequalities                        = AS_RECEIVED;
        static const after_firstInfeasibleSubset         withInfeasibleSubset                    = PROCEED_ALLINEQUALITIES;
        static const theory_deductions                   addTheoryDeductions                     = ONLY_INEQUALITIES;
        static const unsigned                            setCheckInequalitiesToBeginAfter        = 0;
        static const bool                                checkInequalitiesForTrivialSumOfSquares = true;
        static const bool                                checkEqualitiesForTrivialSumOfSquares   = true;
		static const transform_inequalities				 transformIntoEqualities				 = ALL_INEQUALITIES;

		static const bool								 applyNSS								 = false;
        static const unsigned                            maxSDPdegree                            = 4;
        static const unsigned                            SDPupperBoundNrVariables                = 6;
		static const unsigned							 callSDPAfterNMonomials					 = 6;
		static const unsigned							 sternBrocotStartPrecisionOneTo			 = 80;
		static const unsigned							 sternBrocotHigherPrecisionSteps		 = 2;
		static const unsigned							 sternBrocotHigherPrecisionFactor		 = 10;
    };
    
    /*
    struct GBSettings7
    {
        static const unsigned                            identifier                              = 7;
        
        typedef GiNaCRA::GradedLexicgraphic              Order;
        typedef GiNaCRA::MultivariatePolynomialMR<Order> Polynomial;
        typedef GiNaCRA::MultivariateIdeal<Order>        MultivariateIdeal;
        typedef GiNaCRA::BaseReductor<Order>             Reductor;
		typedef smtrat::decidePassingPolynomial			 passPolynomial;

        static const bool                                passGB                                  = true;
        static const bool                                getReasonsForInfeasibility              = false;
        static const bool                                passWithMinimalReasons                  = false;
        static const check_inequalities                  checkInequalities                       = ALWAYS;
        static const pass_inequalities                   passInequalities                        = FULL_REDUCED;
        static const after_firstInfeasibleSubset         withInfeasibleSubset                    = PROCEED_ALLINEQUALITIES;
        static const theory_deductions                   addTheoryDeductions                     = NO_CONSTRAINTS;
        static const unsigned                            setCheckInequalitiesToBeginAfter        = 0;
        static const bool                                checkInequalitiesForTrivialSumOfSquares = true;
        static const bool                                checkEqualitiesForTrivialSumOfSquares   = true;
		static const transform_inequalities				 transformIntoEqualities				 = NO_INEQUALITIES;

		static const bool								 applyNSS								 = false;
        static const unsigned                            maxSDPdegree                            = 4;
        static const unsigned                            SDPupperBoundNrVariables                = 6;
		static const unsigned							 callSDPAfterNMonomials					 = 6;
		static const unsigned							 sternBrocotStartPrecisionOneTo			 = 80;
		static const unsigned							 sternBrocotHigherPrecisionSteps		 = 2;
		static const unsigned							 sternBrocotHigherPrecisionFactor		 = 10;
    };
    
    struct GBSettings0
    {
        static const unsigned                            identifier                              = 0;
        
        typedef GiNaCRA::GradedLexicgraphic              Order;
        typedef GiNaCRA::MultivariatePolynomialMR<Order> Polynomial;
        typedef GiNaCRA::MultivariateIdeal<Order>        MultivariateIdeal;
        typedef GiNaCRA::BaseReductor<Order>             Reductor;
		typedef smtrat::decidePassingPolynomial			 passPolynomial;

        static const bool                                passGB                                  = false;
        static const bool                                getReasonsForInfeasibility              = false;
        static const bool                                passWithMinimalReasons                  = false;
        static const check_inequalities                  checkInequalities                       = NEVER;
        static const pass_inequalities                   passInequalities                        = AS_RECEIVED;
        static const after_firstInfeasibleSubset         withInfeasibleSubset                    = PROCEED_INFEASIBLEANDDEDUCTION;
        static const theory_deductions                   addTheoryDeductions                     = ONLY_INEQUALITIES;
        static const unsigned                            setCheckInequalitiesToBeginAfter        = 0;
        static const bool                                checkInequalitiesForTrivialSumOfSquares = true;
        static const bool                                checkEqualitiesForTrivialSumOfSquares   = true;
		static const transform_inequalities				 transformIntoEqualities				 = NO_INEQUALITIES;

		static const bool								 applyNSS								 = false;
        static const unsigned                            maxSDPdegree                            = 4;
        static const unsigned                            SDPupperBoundNrVariables                = 6;
		static const unsigned							 callSDPAfterNMonomials					 = 6;
		static const unsigned							 sternBrocotStartPrecisionOneTo			 = 80;
		static const unsigned							 sternBrocotHigherPrecisionSteps		 = 2;
		static const unsigned							 sternBrocotHigherPrecisionFactor		 = 10;
    };
    
    struct GBSettings8
    {
        static const unsigned                            identifier                              = 8;
        
        typedef GiNaCRA::GradedLexicgraphic              Order;
        typedef GiNaCRA::MultivariatePolynomialMR<Order> Polynomial;
        typedef GiNaCRA::MultivariateIdeal<Order>        MultivariateIdeal;
        typedef GiNaCRA::BaseReductor<Order>             Reductor;
		typedef smtrat::decidePassingPolynomial			 passPolynomial;

        static const bool                                passGB                                  = true;
        static const bool                                getReasonsForInfeasibility              = true;
        static const bool                                passWithMinimalReasons                  = true;
        static const check_inequalities                  checkInequalities                       = NEVER;
        static const pass_inequalities                   passInequalities                        = AS_RECEIVED;
        static const after_firstInfeasibleSubset         withInfeasibleSubset                    = PROCEED_ALLINEQUALITIES;
        static const theory_deductions                   addTheoryDeductions                     = NO_CONSTRAINTS;
        static const unsigned                            setCheckInequalitiesToBeginAfter        = 0;
        static const bool                                checkInequalitiesForTrivialSumOfSquares = true;
        static const bool                                checkEqualitiesForTrivialSumOfSquares   = true;
		static const transform_inequalities				 transformIntoEqualities				 = ALL_INEQUALITIES;

		static const bool								 applyNSS								 = false;
        static const unsigned                            maxSDPdegree                            = 4;
        static const unsigned                            SDPupperBoundNrVariables                = 6;
		static const unsigned							 callSDPAfterNMonomials					 = 6;
		static const unsigned							 sternBrocotStartPrecisionOneTo			 = 80;
		static const unsigned							 sternBrocotHigherPrecisionSteps		 = 2;
		static const unsigned							 sternBrocotHigherPrecisionFactor		 = 10;
    };
    
    struct GBSettings9
    {
        static const unsigned                            identifier                              = 9;
        
        typedef GiNaCRA::GradedLexicgraphic              Order;
        typedef GiNaCRA::MultivariatePolynomialMR<Order> Polynomial;
        typedef GiNaCRA::MultivariateIdeal<Order>        MultivariateIdeal;
        typedef GiNaCRA::BaseReductor<Order>             Reductor;
		typedef smtrat::decidePassingPolynomial			 passPolynomial;

        static const bool                                passGB                                  = true;
        static const bool                                getReasonsForInfeasibility              = true;
        static const bool                                passWithMinimalReasons                  = true;
        static const check_inequalities                  checkInequalities                       = AFTER_NEW_GB;
        static const pass_inequalities                   passInequalities                        = AS_RECEIVED;
        static const after_firstInfeasibleSubset         withInfeasibleSubset                    = PROCEED_ALLINEQUALITIES;
        static const theory_deductions                   addTheoryDeductions                     = NO_CONSTRAINTS;
        static const unsigned                            setCheckInequalitiesToBeginAfter        = 0;
        static const bool                                checkInequalitiesForTrivialSumOfSquares = true;
        static const bool                                checkEqualitiesForTrivialSumOfSquares   = true;
		static const transform_inequalities				 transformIntoEqualities				 = ONLY_NONSTRICT;

		static const bool								 applyNSS								 = false;
        static const unsigned                            maxSDPdegree                            = 4;
        static const unsigned                            SDPupperBoundNrVariables                = 6;
		static const unsigned							 callSDPAfterNMonomials					 = 6;
		static const unsigned							 sternBrocotStartPrecisionOneTo			 = 80;
		static const unsigned							 sternBrocotHigherPrecisionSteps		 = 2;
		static const unsigned							 sternBrocotHigherPrecisionFactor		 = 10;
    };
    
    struct GBSettings10
    {
        static const unsigned                            identifier                              = 10;
        
        typedef GiNaCRA::GradedLexicgraphic              Order;
        typedef GiNaCRA::MultivariatePolynomialMR<Order> Polynomial;
        typedef GiNaCRA::MultivariateIdeal<Order>        MultivariateIdeal;
        typedef GiNaCRA::BaseReductor<Order>             Reductor;
		typedef smtrat::decidePassingPolynomial			 passPolynomial;

        static const bool                                passGB                                  = false;
        static const bool                                getReasonsForInfeasibility              = true;
        static const bool                                passWithMinimalReasons                  = false;
        static const check_inequalities                  checkInequalities                       = NEVER;
        static const pass_inequalities                   passInequalities                        = AS_RECEIVED;
        static const after_firstInfeasibleSubset         withInfeasibleSubset                    = PROCEED_INFEASIBLEANDDEDUCTION;
        static const theory_deductions                   addTheoryDeductions                     = NO_CONSTRAINTS;
        static const unsigned                            setCheckInequalitiesToBeginAfter        = 0;
        static const bool                                checkInequalitiesForTrivialSumOfSquares = true;
        static const bool                                checkEqualitiesForTrivialSumOfSquares   = true;
		static const transform_inequalities				 transformIntoEqualities				 = NO_INEQUALITIES;

		static const bool								 applyNSS								 = false;
        static const unsigned                            maxSDPdegree                            = 4;
        static const unsigned                            SDPupperBoundNrVariables                = 6;
		static const unsigned							 callSDPAfterNMonomials					 = 6;
		static const unsigned							 sternBrocotStartPrecisionOneTo			 = 80;
		static const unsigned							 sternBrocotHigherPrecisionSteps		 = 2;
		static const unsigned							 sternBrocotHigherPrecisionFactor		 = 10;
    };
    
    struct GBSettings25
    {
        static const unsigned                            identifier                              = 25;
        
        typedef GiNaCRA::GradedLexicgraphic              Order;
        typedef GiNaCRA::MultivariatePolynomialMR<Order> Polynomial;
        typedef GiNaCRA::MultivariateIdeal<Order>        MultivariateIdeal;
        typedef GiNaCRA::BaseReductor<Order>             Reductor;
		typedef smtrat::decidePassingPolynomial			 passPolynomial;

        static const bool                                passGB                                  = true;
        static const bool                                getReasonsForInfeasibility              = true;
        static const bool                                passWithMinimalReasons                  = true;
        static const check_inequalities                  checkInequalities                       = ALWAYS;
        static const pass_inequalities                   passInequalities                        = AS_RECEIVED;
        static const after_firstInfeasibleSubset         withInfeasibleSubset                    = RETURN_DIRECTLY;
        static const theory_deductions                   addTheoryDeductions                     = NO_CONSTRAINTS;
        static const unsigned                            setCheckInequalitiesToBeginAfter        = 0;
        static const bool                                checkInequalitiesForTrivialSumOfSquares = true;
        static const bool                                checkEqualitiesForTrivialSumOfSquares   = true;
		static const transform_inequalities				 transformIntoEqualities				 = NO_INEQUALITIES;

		static const bool								 applyNSS								 = true;
        static const unsigned                            maxSDPdegree                            = 3;
        static const unsigned                            SDPupperBoundNrVariables                = 60;
		static const unsigned							 callSDPAfterNMonomials					 = 6;
		static const unsigned							 sternBrocotStartPrecisionOneTo			 = 80;
		static const unsigned							 sternBrocotHigherPrecisionSteps		 = 2;
		static const unsigned							 sternBrocotHigherPrecisionFactor		 = 10;
    };
    */
    
    
	struct decidePassingPolynomial {
		static bool evaluate (const GBSettings3::Polynomial original, const GBSettings3::Polynomial& reduced) {
			return (original.lterm().tdeg() >= reduced.lterm().tdeg() && original.nrOfTerms() > reduced.nrOfTerms() );
		}
	};
    
}

#endif   /* GBSETTINGS_H */
