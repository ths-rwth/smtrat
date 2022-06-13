/**
 * @file GBPPSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2018-03-09
 * Created on 2018-03-09.
 */

#pragma once

#include <carl-arith/poly/umvpoly/MultivariatePolynomial.h>
#include <carl-arith/groebner/GBProcedure.h>
#include <carl-arith/groebner/gb-buchberger/Buchberger.h>

namespace smtrat
{
	struct GBPPSettings1
	{
		static constexpr auto moduleName = "GBPPModule<GBPPSettings1>"; 
		
		using ReasonPolicy = carl::StdMultivariatePolynomialPolicies<carl::BVReasons>;
		using Order = carl::GrLexOrdering;
		using PolynomialWithReasons = carl::MultivariatePolynomial<Rational, Order, ReasonPolicy>;
		using Groebner = carl::GBProcedure<PolynomialWithReasons, carl::Buchberger, carl::StdAdding>;
		using Reductor = carl::Reductor<PolynomialWithReasons,PolynomialWithReasons>;
		
		//typedef carl::Ideal<PolynomialWithReasons>						     MultivariateIdeal;
		//typedef smtrat::decidePassingPolynomial								 passPolynomial;
	};
}
