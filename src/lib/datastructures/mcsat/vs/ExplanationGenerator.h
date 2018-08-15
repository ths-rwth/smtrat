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
	// TODO as parameter:
	bool reduceConflictConstraints = true;
	bool clauseChainWithEquivalences = true;
	
	boost::optional<FormulaT> generateExplanation() const {
		// generate test candidates
		std::vector<::vs::Substitution> testCandidates;
		if (helper::generateTestCandidates(testCandidates, mTargetVar, mModel, mConstraints)) {
			FormulasT res;
			res.reserve(testCandidates.size());
			for (const auto& tc : testCandidates) {
				FormulasT substitutionResults;
				substitutionResults.reserve(mConstraints.size());

				// substitute tc into each input constraint
				for (const auto& constr : mConstraints) {
					SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substituting " << tc << " into " << constr);

					FormulaT result; // TODO reduceConflictConstraints maybe?
					if (!helper::substitute(constr, tc, mModel, result)) {
						SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Substitution failed");
						return boost::none;
					}

					// check if current constraint is part of the conflict
					if (reduceConflictConstraints) {
						carl::ModelValue<Rational,Poly> eval = carl::model::evaluate(result, mModel);
						// If evaluation result is not a bool, then the model probably contains a RAN or MVRoot. In this case, we just take the constraint in.
						if (!eval.isBool() || !eval.asBool()) {
							SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Use constraint " << constr << " for explanation");
							substitutionResults.push_back(std::move(result));
						}					
						else {
							SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Ignore constraint " << constr << " because it is not part of the conflict");
						}
					}
					else {
						substitutionResults.push_back(std::move(result));
					}

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
			break;

			default:
				assert(false);
		}
	}

	void transformToImplicationChain(const FormulaT& formula, ClauseChain& chain, bool withEquivalences) const {
		FormulaT conflictingClause = _transformToImplicationChain(formula, chain, withEquivalences);
		chain.appendConflicting(std::move(conflictingClause));
	}

public:
	boost::optional<mcsat::Explanation> getExplanation() const {
		auto expl = generateExplanation();

		if (expl) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Obtained explanation " << (*expl));

			SMTRAT_LOG_DEBUG("smtrat.mcsat.vs", "Transforming to implication chain");
			ClauseChain chain;
			transformToImplicationChain(*expl, chain, clauseChainWithEquivalences);
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
