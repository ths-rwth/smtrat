/** 
 * @file:   ApplyRules.h
 * @author: Sebastian Junges
 *
 * @since March 13, 2014
 */

#pragma once

#include "UsingDeclarations.h"

namespace smtrat
{
	namespace groebner
	{	
		typedef std::map<carl::Variable, std::pair<TermT, carl::BitVector> > RewriteRules;
		
		template<typename Polynomial>
		static Polynomial rewritePolynomial(const Polynomial& inputPolynomial, const RewriteRules& rules)
		{
			std::map<carl::Variable, TermT> substitutions;

			carl::carlVariables vars;
			carl::BitVector resultingReasons;
			if( Polynomial::has_reasons )
			{
				resultingReasons = inputPolynomial.getReasons();
				vars = carl::variables(inputPolynomial);
			}

			for(auto rule : rules)
			{
				substitutions.insert(std::make_pair(rule.first, rule.second.first));
				if(Polynomial::has_reasons && vars.has(rule.first))
				{
					resultingReasons.calculateUnion(rule.second.second);
				}
			}
			Polynomial result = carl::substitute(inputPolynomial, substitutions);
			result.setReasons(resultingReasons);
			return result;
		}
	}
}