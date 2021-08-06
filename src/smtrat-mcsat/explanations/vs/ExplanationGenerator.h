#pragma once

#include "VSHelper.h"

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
			freeVariables.insert(constr.variables().begin(), constr.variables().end());
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

	boost::optional<FormulaT> eliminateVariable(const FormulaT& inputFormula, const carl::Variable& var) const {
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
							return boost::none;
						}

						// check if current constraint is part of the conflict
						if (Settings::reduceConflictConstraints) {
							carl::ModelValue<Rational,Poly> eval = carl::model::evaluate(substitutionResult, mModel);
							// If constraint is not fully evaluated or evaluates to false, we take it in.
							std::cout << substitutionResult << " " << mModel << " " << eval.isBool() << " " << eval.asBool() << std::endl;
							if (!eval.isBool() || !eval.asBool()) {
								SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Use constraint " << constr << " for explanation");
							}					
							else {
								SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Ignore constraint " << constr << " because it is not part of the conflict");
								substitutionResult = FormulaT(carl::FormulaType::TRUE);
							}
						}

						// substitute into formula
						carl::FormulaSubstitutor<FormulaT> substitutor;
						branchResult = substitutor.substitute(branchResult, constr, substitutionResult);
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
				if (res.back() == FormulaT(carl::FormulaType::TRUE)) std::exit(124);
				assert(res.back() != FormulaT(carl::FormulaType::TRUE));
			}

			return FormulaT(carl::FormulaType::OR, std::move(res));
		}
		else {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Could not generate test candidates");
			return boost::none;
		}
	}

	boost::optional<FormulaT> eliminateVariables() const {
		// eliminate unassigned variables
		boost::optional<FormulaT> res = FormulaT(carl::FormulaType::AND, mConstraints);
		auto unassignedVariables = getUnassignedVariables();
		for (auto iter = unassignedVariables.first; iter != unassignedVariables.second; iter++) {
			res = eliminateVariable(*res, *iter);
			if (!res) {
				return boost::none;
			}
			assert(res->variables().find(*iter) == res->variables().end());
		}

		#ifndef NDEBUG
		carl::ModelValue<Rational,Poly> evalRes = carl::model::evaluate(*res, mModel);
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

	/**
	 * Transforms a given Boolean conjunction over AND and OR to CNF via Tseitin-Transformation
	 * so that, if the input formula is conflicting under the current assignment, after all clauses
	 * in "implications" have been propagated in the given order, the returned formula evaluates to false.
	 */
	FormulaT _transformToImplicationChain(const FormulaT& formula, ClauseChain& chain, bool withEquivalences) const /*__attribute__((noinline))*/ {
		switch(formula.getType()) {
			case carl::FormulaType::TRUE:
			case carl::FormulaType::FALSE:
			case carl::FormulaType::CONSTRAINT:
			case carl::FormulaType::VARCOMPARE:
			case carl::FormulaType::VARASSIGN:
			{
				return formula;
			}
			break;

			case carl::FormulaType::OR:
			{
				FormulasT newFormula;
				for (const auto& sub : formula.subformulas()) {
					FormulaT tseitinSub = _transformToImplicationChain(sub, chain, withEquivalences);
					newFormula.push_back(std::move(tseitinSub));
				}
				return FormulaT(carl::FormulaType::OR, std::move(newFormula));
			}
			break;

			case carl::FormulaType::AND:
			{
				FormulaT tseitinVar = chain.createTseitinVar(formula);
				FormulasT newFormula;
				for (const auto& sub : formula.subformulas()) {
					FormulaT tseitinSub = _transformToImplicationChain(sub, chain, withEquivalences);
					newFormula.push_back(std::move(tseitinSub));
					const auto& lit = newFormula.back();

					// tseitinVar -> newFormula_1 && ... && newFormula_n

					carl::ModelValue<Rational,Poly> eval = carl::model::evaluate(sub, mModel);
					assert(eval.isBool());
					if (!eval.asBool()) {
						chain.appendPropagating(FormulaT(carl::FormulaType::OR, FormulasT({lit, tseitinVar.negated()})), tseitinVar.negated());
					} else {
						chain.appendOptional(FormulaT(carl::FormulaType::OR, FormulasT({lit, tseitinVar.negated()})));
					}
				}

				if (withEquivalences) {
					// newFormula_1 && ... && newFormula_n -> tseitinVar
					FormulasT tmp;
					std::transform (newFormula.begin(), newFormula.end(), std::back_inserter(tmp), [](const FormulaT& f) -> FormulaT { return f.negated(); } );
					tmp.push_back(tseitinVar);
					chain.appendOptional(FormulaT(carl::FormulaType::OR, tmp));
				}
				
				return tseitinVar;
			}

			default:
				SMTRAT_LOG_WARN("smtrat.mcsat.vs", "Invalid formula type " << formula);
				assert(false);
				return FormulaT();
		}
	}

	void transformToImplicationChain(const FormulaT& formula, ClauseChain& chain, bool withEquivalences) const {
		FormulaT conflictingClause = _transformToImplicationChain(formula, chain, withEquivalences);
		chain.appendConflicting(std::move(conflictingClause));
	}

public:
	boost::optional<mcsat::Explanation> getExplanation() const {
		auto expl = eliminateVariables();

		if (expl) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Obtained explanation " << (*expl));

			SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Transforming to implication chain");
			ClauseChain chain;
			transformToImplicationChain(*expl, chain, Settings::clauseChainWithEquivalences);
			SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Got clauses " << chain);

			return mcsat::Explanation(std::move(chain));
		} else {
			return boost::none;
		}
	}
};

}
}
}
