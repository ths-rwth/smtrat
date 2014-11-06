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

			std::set<carl::Variable> vars;
			carl::BitVector resultingReasons;
			if( Polynomial::has_reasons )
			{
				resultingReasons = inputPolynomial.getReasons();
				vars = inputPolynomial.gatherVariables();
			}

			for(auto rule : rules)
			{
				substitutions.insert(std::make_pair(rule.first, rule.second.first));
				if(Polynomial::has_reasons && vars.count(rule.first) == 1)
				{
					resultingReasons.calculateUnion(rule.second.second);
				}
			}
			Polynomial result = inputPolynomial.substitute(substitutions);
			result.setReasons(resultingReasons);
			return result;
		}
	}
}