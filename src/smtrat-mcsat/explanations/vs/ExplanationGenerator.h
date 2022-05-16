#pragma once

#include "VSHelper.h"
#include <carl-formula/formula/functions/Substitution.h>

#include <smtrat-mcsat/smtrat-mcsat.h>

namespace smtrat {
namespace mcsat {
namespace vs {

struct DefaultSettings {
	static const bool reduceConflictConstraints = true;
	static const bool clauseChainWithEquivalences = false;
};

template<class Settings>
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

	std::pair<std::vector<carl::Variable>::const_iterator, std::vector<carl::Variable>::const_iterator> getUnassignedVariables() const {
		std::unordered_set<carl::Variable> freeVariables;
		for (const auto& constr : mConstraints) {
			auto vars = carl::variables(constr);
			freeVariables.insert(vars.begin(), vars.end());
		}
		
		auto firstVar = std::find(mVariableOrdering.begin(), mVariableOrdering.end(), mTargetVar);
		assert(firstVar != mVariableOrdering.end());
		auto lastVar = firstVar;
		for (auto iter = firstVar; iter != mVariableOrdering.end(); iter++) {
			if (freeVariables.find(*iter) != freeVariables.end()) {
				lastVar = iter;
			}
		}

		lastVar++;
		
		return std::make_pair(firstVar, lastVar); 
	}

	std::optional<FormulaT> eliminateVariable(const FormulaT& inputFormula, const carl::Variable& var) const {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Eliminating variable " << var << " in " << inputFormula);

		// get formula atoms
		FormulaSetT atoms;
		helper::getFormulaAtoms(inputFormula, atoms);

		// generate test candidates
		std::vector<helper::TestCandidate> testCandidates;
		if (helper::generateTestCandidates(testCandidates, var, atoms)) {
			FormulasT res;
			res.reserve(testCandidates.size());
			for (const auto& tc : testCandidates) {
				FormulaT branchResult = inputFormula;

				// substitute tc into each input constraint
				for (const auto& constr : atoms) {
					// check if branchResult still contains constr
					//if (branchResult.contains(constr)) {
						SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substituting " << tc.term << " for " << var << " into " << constr);

						// calculate substitution
						FormulaT substitutionResult; // TODO reduceConflictConstraints?
						if (!helper::substitute(constr, var, tc.term, substitutionResult)) {
							SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substitution failed");
							return std::nullopt;
						}

						// check if current constraint is part of the conflict
						if (Settings::reduceConflictConstraints) {
							carl::ModelValue<Rational,Poly> eval = carl::evaluate(substitutionResult, mModel);
							// If constraint is not fully evaluated or evaluates to false, we take it in.
							if (!eval.isBool() || !eval.asBool()) {
								SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Use constraint " << constr << " for explanation");
							}					
							else {
								SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Ignore constraint " << constr << " because it is not part of the conflict");
								substitutionResult = FormulaT(carl::FormulaType::TRUE);
							}
						}

						// substitute into formula
						branchResult = carl::substitute(branchResult, constr, substitutionResult);
					//}
				}

				// add side condition
				FormulasT branch;
				branch.push_back(std::move(branchResult));				
				for (const auto& sc : tc.side_condition) {
					branch.emplace_back(sc);
				}
				
				res.emplace_back(carl::FormulaType::AND, std::move(branch));
				SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substitution of " << tc.term << " into formula obtained " << res.back());
				assert(res.back() != FormulaT(carl::FormulaType::TRUE));
			}

			return FormulaT(carl::FormulaType::OR, std::move(res));
		}
		else {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Could not generate test candidates");
			return std::nullopt;
		}
	}

	std::optional<FormulaT> eliminateVariables() const {
		// eliminate unassigned variables
		std::optional<FormulaT> res = FormulaT(carl::FormulaType::AND, mConstraints);
		auto unassignedVariables = getUnassignedVariables();
		for (auto iter = unassignedVariables.first; iter != unassignedVariables.second; iter++) {
			res = eliminateVariable(*res, *iter);
			if (!res) {
				return std::nullopt;
			}
			assert(res->variables().find(*iter) == res->variables().end());
		}

		#ifndef NDEBUG
		carl::ModelValue<Rational,Poly> evalRes = carl::evaluate(*res, mModel);
		assert(evalRes.isBool());
		assert(!evalRes.asBool());
		#endif

		// collect input constraints
		FormulasT expl;
		expl.push_back(std::move(*res));
		for (const auto& c: mConstraints) {
			expl.emplace_back(c.negated());
		}
		return FormulaT(carl::FormulaType::OR, expl);
    }

public:
	std::optional<mcsat::Explanation> getExplanation() const {
		auto expl = eliminateVariables();

		if (expl) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Obtained explanation " << (*expl));
			SMTRAT_VALIDATION_ADD("smtrat.mcsat.vs", "explanation", expl->negated(), false);
			return mcsat::Explanation(ClauseChain::from_formula(*expl, mModel, Settings::clauseChainWithEquivalences));
		} else {
			return std::nullopt;
		}
	}
};

}
}
}
