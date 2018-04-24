#pragma once

#include "../../../Common.h"

#include "VSHelper.h"

#include <carl/util/Common.h>


namespace smtrat {
namespace mcsat {
namespace vs {


class ExplanationGenerator {
private:
	const std::vector<FormulaT>& mConstraints;
	const std::vector<carl::Variable>& mVariableOrdering; 
	const carl::Variable& mTargetVar;
	const Model& mModel;
    
public:
	ExplanationGenerator(const std::vector<FormulaT>& constraints, const std::vector<carl::Variable>& variableOrdering, const carl::Variable& targetVar, const Model& model):
		mConstraints(constraints),
		mVariableOrdering(variableOrdering),
		mTargetVar(targetVar),
		mModel(model)
	{}

private:
	
	boost::optional<FormulaT> generateExplanation() const {
		// get constraints from formula
		std::vector<const ConstraintT*> constraints;
		for (auto constr = mConstraints.begin(); constr != mConstraints.end(); ++constr) {
			assert(constr->getType() == carl::FormulaType::CONSTRAINT);
			constraints.push_back(&(constr->constraint()));
		}

		// generate test candidates
		std::vector<::vs::Substitution> testCandidates;
		if (helper::generateTestCandidates(testCandidates, mTargetVar, constraints)) {
			FormulasT res;
			for (auto tc = testCandidates.begin(); tc != testCandidates.end(); ++tc) {
				// substitute tc into each input constraint
				FormulasT substitutionResults;

				for (auto constr = mConstraints.begin(); constr != mConstraints.end(); ++constr) {
					const ConstraintT& constraint = constr->constraint();
					::vs::DisjunctionOfConstraintConjunctions result;
					carl::Variables dummy_vars; // we do not make use of this feature here
					smtrat::EvalDoubleIntervalMap dummy_map;
            		bool success = substitute(constraint, *tc, result, false, dummy_vars, dummy_map);
					if (!success) {
						return boost::none;
					}
					substitutionResults.push_back(helper::doccToFormula(result));
				}
				
				res.emplace_back(carl::FormulaType::AND, std::move(substitutionResults));
			}
			return FormulaT(carl::FormulaType::OR, std::move(res));
		}
		else {
			return boost::none;
		}
    }

public:
	boost::optional<FormulaT> getExplanation(const FormulaT& f) const {
		// this module only explains conflicts
		// assert( f == FormulaT( ConstraintT( false ) ) );
		assert(f == FormulaT(carl::FormulaType::FALSE));
        return generateExplanation();
	}
};

}
}
}
