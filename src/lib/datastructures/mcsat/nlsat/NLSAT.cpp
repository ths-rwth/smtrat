#include "NLSAT.h"

#include "ExplanationGenerator.h"
#include "LemmaBuilder.h"

#include <carl/util/variant_util.h>
#include <carl/util/vector_util.h>

#include <algorithm>

namespace smtrat {
namespace nlsat {

FormulaT NLSAT::resolveNegation(const FormulaT& f) const {
	assert(f.getType() == carl::FormulaType::NOT);
	SMTRAT_LOG_DEBUG("smtrat.nlsat", "Resolving negation of " << f);
	switch (f.subformula().getType()) {
		case carl::FormulaType::CONSTRAINT: {
			const auto& c = f.subformula().constraint();
			return FormulaT(c.lhs(), carl::invertRelation(c.relation()));
		}
		case carl::FormulaType::VARCOMPARE:
			return FormulaT(f.subformula().variableComparison().negation());
		default:
			SMTRAT_LOG_ERROR("smtrat.nlsat", "Invalid formula type inside a negation: " << f);
			assert(false);
	}
	return FormulaT();
}

void NLSAT::pushConstraint(const FormulaT& f) {
	SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding " << f);
	switch (f.getType()) {
		case carl::FormulaType::NOT:
			switch (f.subformula().getType()) {
				case carl::FormulaType::CONSTRAINT:
					mConstraints.emplace_back(f);
					break;
				case carl::FormulaType::VARCOMPARE:
					mMVBounds.emplace_back(f.subformula().variableComparison().negation());
					break;
				default:
					SMTRAT_LOG_ERROR("smtrat.nlsat", "Invalid formula type inside a negation: " << f);
					assert(false);
			}
			break;
		case carl::FormulaType::CONSTRAINT:
			mConstraints.emplace_back(f);
			break;
		case carl::FormulaType::VARCOMPARE:
			mMVBounds.emplace_back(f);
			break;
		default:
			SMTRAT_LOG_ERROR("smtrat.nlsat", "Invalid formula type for a constraint: " << f);
			assert(false);
	}
}

void NLSAT::popConstraint(const FormulaT& f) {
	SMTRAT_LOG_DEBUG("smtrat.nlsat", "Removing " << f);
	switch (f.getType()) {
		case carl::FormulaType::NOT:
			switch (f.subformula().getType()) {
				case carl::FormulaType::CONSTRAINT:
					assert(mConstraints.back() == f);
					mConstraints.pop_back();
					break;
				case carl::FormulaType::VARCOMPARE:
					assert(mMVBounds.back() == FormulaT(f.subformula().variableComparison().negation()));
					mMVBounds.pop_back();
					break;
				default:
					SMTRAT_LOG_ERROR("smtrat.nlsat", "Invalid formula type inside a negation: " << f);
					assert(false);
			}
			break;
		case carl::FormulaType::CONSTRAINT:
			assert(mConstraints.back() == f);
			mConstraints.pop_back();
			break;
		case carl::FormulaType::VARCOMPARE:
			assert(mMVBounds.back() == f);
			mMVBounds.pop_back();
			break;
		default:
			SMTRAT_LOG_ERROR("smtrat.nlsat", "Invalid formula type for a constraint: " << f);
			assert(false);
	}
	
}

void NLSAT::pushAssignment(carl::Variable v, const ModelValue& mv, const FormulaT& f) {
	SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding " << v << " = " << mv);
        if(mModel.find(v) != mModel.end()) {
            std::exit(27);
        }
	assert(mModel.find(v) == mModel.end());
	mModel.emplace(v, mv);
	mVariables.emplace_back(v);
	mAssignments.emplace_back(f);
}

void NLSAT::popAssignment(carl::Variable v) {
	SMTRAT_LOG_DEBUG("smtrat.nlsat", "Removing " << v << " = " << mModel.evaluated(v));
	assert(!mVariables.empty() && mVariables.back() == v);
	mModel.erase(v);
	mVariables.pop_back();
	mAssignments.pop_back();
}

AssignmentFinder::AssignmentOrConflict NLSAT::findAssignment(carl::Variable var) const {
	SMTRAT_LOG_DEBUG("smtrat.nlsat", "Looking for an assignment for " << var);
	AssignmentFinder af(var, mModel);
        FormulasT conflict;
	for (const auto& c: mConstraints) {
		if (c.getType() == carl::FormulaType::NOT) {
			const auto& constraint = c.subformula().constraint();
                        if(!af.addConstraint(FormulaT(constraint.lhs(), carl::invertRelation(constraint.relation())))) {
                            conflict.push_back(FormulaT(constraint.lhs(), carl::invertRelation(constraint.relation())));
                            SMTRAT_LOG_DEBUG("smtrat.nlsat", "No Assignment, built conflicting core " << conflict << " under model " << mModel);
                            return conflict;
                        }
		} else {
			if(!af.addConstraint(c)){
                            conflict.push_back(c);
                            SMTRAT_LOG_DEBUG("smtrat.nlsat", "No Assignment, built conflicting core " << conflict << " under model " << mModel);
                            return conflict;
                        }
		}
	}
	for (const auto& b: mMVBounds) af.addMVBound(b);
	SMTRAT_LOG_DEBUG("smtrat.nlsat", "Calling AssignmentFinder...");
	return af.findAssignment();
}

boost::optional<FormulasT> NLSAT::isInfeasible(carl::Variable var, const FormulaT& f) {
	SMTRAT_LOG_DEBUG("smtrat.nlsat", "Checking whether " << f << " is feasible");
	pushConstraint(f);
	auto res = findAssignment(var);
	popConstraint(f);
	if (carl::variant_is_type<ModelValue>(res)) {
		SMTRAT_LOG_DEBUG("smtrat.nlsat", f << " is feasible");
		return boost::none;
	}
	SMTRAT_LOG_DEBUG("smtrat.nlsat", f << " is infeasible with reason " << boost::get<FormulasT>(res));
	return boost::get<FormulasT>(res);
}

FormulaT NLSAT::explain(carl::Variable var, const FormulasT& reason, const FormulaT& implication) {
	SMTRAT_LOG_DEBUG("smtrat.nlsat", "Explaining " << implication << " by " << reason);
	std::vector<carl::Variable> orderedVars(mVariables.begin(), mVariables.end());
	orderedVars.push_back(var);
	std::reverse(orderedVars.begin(), orderedVars.end());
	
	//FormulasT explanation;
	ExplanationGenerator eg(reason, orderedVars, mModel);
	return eg.getExplanation(implication);
	//LemmaBuilder lb(carl::vector_zip(mVariables, mAssignments), implication, eg);
	//lb.generateLemmas([&explanation](const auto& f){ explanation.emplace_back(f); }, LemmaStrategy::ORIGINAL);
	
	//return FormulaT(carl::FormulaType::OR, std::move(explanation));
}

}
}
