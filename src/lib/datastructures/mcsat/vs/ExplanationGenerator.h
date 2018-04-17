#pragma once

#include "../../../Common.h"

#include "VSHelper.h"

#include <carl/util/Common.h>


namespace smtrat {
namespace mcsat {
namespace vs {


class ExplanationGenerator {
private:
	using RAN = carl::RealAlgebraicNumber<Rational>;
	struct McsatVsSettings {	
		using RegionDescr = regiondescr::lowerbound;
		using BreakHeuristic = breakheuristic::none;
		using RepresentativeChoice = representativechoice::first;
	};

	const Model& mModel;
	const std::vector<FormulaT>& mConstraints;
	const carl::Variable& mTargetVar;
	const std::vector<carl::Variable>& mVariableOrdering; 
    
public:
	ExplanationGenerator(const std::vector<FormulaT>& constraints, const std::vector<carl::Variable>& variableOrdering, const carl::Variable& targetVar, const Model& model):
		mModel(model),
		mConstraints(constraints),
		mTargetVar(targetVar)
	{}

private:
	
	boost::optional<FormulaT> generateExplanation() const
	{
		// get constraints from formula
		std::vector<vs::ConstraintT*> constraints;
		for (auto constr = mConstraints.begin(); constr != mConstraints.end(); ++constr)
		{
			assert(constr->getType() == carl::FormulaType::CONSTRAINT)
			constraints.push_back(&(constr->constraint()));
		}

		// generate test candidates
		std::vector<vs::Substitution> testCandidates;
		if (helper::generateTestCandidates(testCandidates, mTargetVar, constraints))
		{
			FormulasT res;
			for (auto tc = testCandidates.begin(); tc != testCandidates.end(); ++tc)
			{
				// substitute tc into each input constraint
				FormulasT substitutionResults;

				for (auto constr = mConstraints.begin(); constr != mConstraints.end(); ++constr)
				{
					ConstraintT& constraint = constr->constraint();
					DisjunctionOfConstraintConjunctions result;
            		bool success = substitute(constraint, tc, result, false, carl::Variables(), smtrat::EvalDoubleIntervalMap());
					if (!success)
					{
						return boost::none;
					}
					substitutionResults.push_back(helper::doccToFormula(result));
				}
				
				res.emplace_back(carl::FormulaType::AND, std::move(substitutionResults));
			}
			return FormulaT(carl::FormulaType::OR, std::move(res));
		}
		else
		{
			return boost::none;
		}
    }

public:
	boost::optional<FormulaT> getExplanation(const FormulaT& f) const
	{
		// this module only explains conflicts
		assert( f != FormulaT( ConstraintT( false ) ) );

        return generateExplanation();
	}
	
	
};

}
}
}
