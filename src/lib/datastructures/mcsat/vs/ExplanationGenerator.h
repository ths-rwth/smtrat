#pragma once

// #include "../../../Common.h"
// #include <carl/util/Common.h>

#include "VSHelper.h"




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
		// generate test candidates
		std::vector<::vs::Substitution> testCandidates; // TODO size: at most 2*mConstraints.size()
		if (helper::generateTestCandidates(testCandidates, mTargetVar, mModel, mConstraints)) {
			FormulasT res;
			res.reserve(testCandidates.size());
			for (const auto& tc : testCandidates) {
				FormulasT substitutionResults;
				substitutionResults.reserve(mConstraints.size());

				// substitute tc into each input constraint
				for (const auto& constr : mConstraints) {
					SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substituting " << tc << " into " << constr);

					FormulaT result;
					if (!helper::substitute(constr, tc, mModel, result)) {
						SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substitution failed");
						return boost::none;
					}
					substitutionResults.push_back(std::move(result));
					
					if (substitutionResults.back() == FormulaT(carl::FormulaType::FALSE)) {
						break; // since this is part of a conjunction, and we got false, we can ignore future substitutions
					}
				}

				// add side condition
				for (const auto& sc : tc.sideCondition()) {
					substitutionResults.emplace_back(sc);
				}
				
				res.emplace_back(carl::FormulaType::AND, std::move(substitutionResults));
				SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substitution of " << tc << " into formula obtained " << res.back());
				assert(res.back() != FormulaT(carl::FormulaType::TRUE));
			}

			#ifndef NDEBUG
			FormulaT tmp(carl::FormulaType::OR, std::move(res));
			carl::ModelValue<Rational,Poly> evalRes = carl::model::evaluate(tmp, mModel);
			assert(evalRes.isBool());
			assert(!evalRes.asBool());
			#endif

			// collect input constraints
			for (const auto& c: mConstraints) {
				res.emplace_back(c.negated());
			}

			return FormulaT(carl::FormulaType::OR, std::move(res));
		}
		else {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Could not generate test candidates");
			return boost::none;
		}
    }

public:
	boost::optional<FormulaT> getExplanation(const FormulaT& f) const {
		// this module only explains conflicts
		assert(f == FormulaT(carl::FormulaType::FALSE));
        return generateExplanation();
	}
};

}
}
}
