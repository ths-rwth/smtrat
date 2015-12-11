#include <iostream>
#include <stdio.h>
#include "../lib/modules/ICPModule/ContractionCandidateManager.h"
#include "carl/util/stringparser.h"
#include "carl/core/MultivariateHorner.h"
#include "carl/core/MultivariatePolynomial.h"


int main( int argc, const char* argv[] )
{	

	//carl::FastMap<smtrat::Poly, smtrat::Contractor<carl::SimpleNewton>> mContractors;

	
	carl::StringParser sp;
	sp.setVariables({"x", "y", "z"});
	smtrat::Poly p1 = sp.carl::StringParser::parseMultivariatePolynomial<smtrat::Rational>("2*x^4+8*x^7+5*x^2+2*x+3*y^3+2*y^2+4*z^5+2*z^1+8*z^12");
	
	//carl::MultivariateHorner< smtrat::Poly, carl::GREEDY_Is > (std::move(p1));	
	carl::Contraction<carl::SimpleNewton,carl::MultivariateHorner<smtrat::Poly, carl::GREEDY_Is>>( carl::MultivariateHorner< smtrat::Poly, carl::GREEDY_Is > (std::move(p1)) );

 	//smtrat::Contractor<carl::SimpleNewton>(sp.carl::StringParser::parseMultivariatePolynomial<smtrat::Rational>("2*x^4+8*x^7+5*x^2+2*x+3*y^3+2*y^2+4*z^5+2*z^1+8*z^12"));

 	std::cout << "It worked" << std::endl;

}
