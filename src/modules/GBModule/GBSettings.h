/*
 * File:   GBSettings.h
 * Author: square
 *
 * Created on June 18, 2012, 7:50 PM
 */

#include <ginacra/MultivariatePolynomialMR.h>

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
	
	
	struct decidePassingPolynomial;

	struct GBSettings
    {
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
        static const after_firstInfeasibleSubset         withInfeasibleSubset                    = PROCEED_INFEASIBLEANDDEDUCTION;
        static const theory_deductions                   addTheoryDeductions                     = ONLY_INEQUALITIES;
        static const unsigned                            setCheckInequalitiesToBeginAfter        = 0;
        static const bool                                checkInequalitiesForTrivialSumOfSquares = true;
        static const bool                                checkEqualitiesForTrivialSumOfSquares   = true;
		static const bool								 transformIntoEqualities				 = NO_INEQUALITIES;

		static const bool								 applyNSS								 = false;
        static const unsigned                            maxSDPdegree                            = 4;
        static const unsigned                            SDPupperBoundNrVariables                = 6;
		static const unsigned							 callSDPAfterNMonomials					 = 6;
		static const unsigned							 sternBrocotStartPrecisionOneTo			 = 80;
		static const unsigned							 sternBrocotHigherPrecisionSteps		 = 4;
		static const unsigned							 sternBrocotHigherPrecisionFactor		 = 10;
    };
	 
	struct decidePassingPolynomial {
		static bool evaluate (const GBSettings::Polynomial original, const GBSettings::Polynomial& reduced) {
			return (original.lterm().tdeg() >= reduced.lterm().tdeg() && 3 * original.nrOfTerms() <  reduced.nrOfTerms() );
		}
	};
 
	
	
    struct GBSettings8
    {
        typedef GiNaCRA::GradedLexicgraphic              Order;
        typedef GiNaCRA::MultivariatePolynomialMR<Order> Polynomial;
        typedef GiNaCRA::MultivariateIdeal<Order>        MultivariateIdeal;
        typedef GiNaCRA::BaseReductor<Order>             Reductor;

        static const bool                                passGB                                  = true;
        static const bool                                getReasonsForInfeasibility              = true;
        static const bool                                passWithMinimalReasons                  = true;
        static const check_inequalities                  checkInequalities                       = AFTER_NEW_GB;
        static const pass_inequalities                   passInequalities                        = FULL_REDUCED;
        static const after_firstInfeasibleSubset         withInfeasibleSubset                    = PROCEED_ALLINEQUALITIES;
        static const theory_deductions                   addTheoryDeductions                     = ONLY_INEQUALITIES;
        static const unsigned                            setCheckInequalitiesToBeginAfter        = 0;
        static const bool                                checkInequalitiesForTrivialSumOfSquares = true;
        static const bool                                checkEqualitiesForTrivialSumOfSquares   = true;
		static const bool								 transformIntoEqualities				 = false;

        static const unsigned                            maxSDPdegree                            = 4;
        static const unsigned                            SDPupperBoundNrVariables                = 6;
		static const unsigned							 sternBrocotStartPrecisionOneTo			 = 1000;
		static const unsigned							 sternBrocotHigherPrecisionSteps		 = 4;
		static const unsigned							 sternBrocotHigherPrecisionFactor		 = 10;
    };
}

#endif   /* GBSETTINGS_H */
