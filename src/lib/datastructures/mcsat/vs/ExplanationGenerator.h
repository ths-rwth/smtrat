#pragma once

#include "../../../Common.h"

#include "VSHelper.h"

#include <carl/util/Common.h>


namespace smtrat {
namespace mcsat {
namespace vs {

struct SymbolicZero {
	smtrat::SqrtEx sqrtExpression;
	ConstraintsT sideConditions;

	SymbolicZero(smtrat::SqrtEx sqrtExpression, ConstraintsT sideConditions):
		sqrtExpression(sqrtExpression),
		sideConditions(sideConditions)
	{
	}
}

/**
 * Functions returning formulas describing the region represented by the current variable and assignment.
 */
namespace regiondescr {
	struct lowerbound { // according to Def 3.3
		FormulaT operator()(const carl::Variable& var, const vs::Substitution& substitution, const Model& model, const std::vector<vs::SymbolicZeros>& zeros) {
			// TODO

			switch(substitution.type())
			{
				case vs::Substitution::Type::MINUS_INFINITY:
					smtrat::FormulasT subformulas;
					for (auto zero = zeros.begin(); zero != zeros.end(); ++zero)
					{
						smtrat::FormulaT sideCond(carl::FormulaType::AND, zero->sideConditions);
						smtrat::Poly xSmallerThanZeroPol = var - zero->sqrtExpression; // TODO substitute sqrtExpr into formula
						ConstraintT xSmallerThanZeroConstr(xSmallerThanZeroPol, carl::Relation:LESS);
						smtrat::FormulaT xSmallerThanZero(xSmallerThanZeroConstr);
						subformulas.emplace_back(carl::FormulaType::IMPLIES, sideCond, xSmallerThanZero);
					}
					return smtrat::FormulaT(carl::FormulaType::AND, subformulas);
				case vs::Substitution::Type::NORMAL:

					break;
				case vs::Substitution::Type::PLUS_EPSILON:

					break;
				default:
					assert(false);
			}
    	}
	};

    struct lowerupperbounds {
		FormulaT operator()(const carl::Variable& var, const vs::Substitution& substitution, const Model& model, const std::vector<vs::SymbolicZeros>& zeros) {
			// TODO
    	}
	};

	struct allzeros {
		FormulaT operator()(const carl::Variable& var, const vs::Substitution& substitution, const Model& model, const std::vector<vs::SymbolicZeros>& zeros) {
			// TODO
    	}
	};
}

namespace breakheuristic {
	struct none {
		bool operator()() {
			return false;
    	}
	};

	struct representedByTestCandidate {
		bool operator()() {
			// TODO
    	}
	};
}

namespace representativechoice {    
    struct first {
		int operator()() {
			// TODO
    	}
	};
}

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

	carl::IDPool mpConditionIdAllocator; // TODO was ist das?
    
public:
	ExplanationGenerator(const std::vector<FormulaT>& constraints, const std::vector<carl::Variable>& variableOrdering, const carl::Variable& targetVar, const Model& model):
		mModel(model),
		mConstraints(constraints),
		mTargetVar(targetVar)
	{}

private:

	void getConditionsFromConstraints(std::vector<vs::Condition>& result, const std::vector<FormulaT>& constraints) const
    {
		for (auto constr = constraints.begin(); constr != constraints.end(); ++constr)
		{
			assert(constr->getType() == carl::FormulaType::CONSTRAINT)
			result.emplace_back(constr->constraint(), mpConditionIdAllocator->get());
		}
    }

	/**
     * Get a representative for the given variable under the current assignment.
	 * Returns false iff VS is not applicable.
     */
    bool chooseRepresenative(const std::vector<ConditionsT*>& conditions, const carl::variable& eliminationVar, vs::Substitution& result, std::vector<SymbolicZero>& symbolicZeros) const {
        ConstraintsT sideCondition;
        SqrtEx sqrtExpression;

        for (auto condition = conditions.begin(); condition != conditions.end(); ++condition)
        {
            const ConstraintT& constraint = (*condition)->constraint();

            bool res = generateZeros(constraint, eliminationVar, [&](const SqrtEx&& sqrtExpression, const ConstraintsT&& sideConditions)) {
                // check if valid under current model
				//carl::model::evaluate(mModel, )
                if (/*TODO check if sideCondition is valid*/)
                {
                    // TODO compare sqrtExpression with current best representative under current model
					// TODO use heuristic
				}

				// collect zeros
				symbolicZeros.emplace_back(sqrtExpression, sideConditions);
            });

			if (!res) {
				return false;
			}
        }

		result = vs::Substitution(/*TODO winner */);

		return true;
    }
	
	FormulaT generatePath(const FormulaT& inputFormula) const
	{
		// get the variable to eliminate
		std::vector<carl::Variable>::reverse_iterator currentVar = std::find(mVariableOrdering.rbegin(), mVariableOrdering.rend(), mTargetVar);
		
		FormulaT currentFormula(formula);

		FormulasT regionDescriptions;

		while (++currentVar != mVariableOrdering.rend())
		{
			// if currentVar is notr contained in currentFormula, skip to the next variable
			const Variables& currentFormulaVars = currentFormula.variables();
			if (std::find(currentFormulaVars.begin(), currentFormulaVars.end(), *currentVar) == currentFormulaVars.end())
			{
				continue;
			}

			// get conditions from formula
			std::vector<vs::Condition> initialConditions;
			getConditionsFromConstraints(initialConditions, mConstraints);
			std::vector<vs::Condition*> conditions;
			// convert to vector of pointers:
			for (auto it = initialConditions.begin(); it != initialConditions.end(); ++it)
			{
				conditions.push_back(&(*it));
			}

			// choose representative 
			vs::Substitution representative;
			std::vector<SymbolicZero> symbolicZeros;
			// TODO maybe collect all zeros and then choose representative
			bool res = chooseRepresenative(conditions, *currentVar, representative, symbolicZeros);
			if (!res)
			{
				return false;
			}

			// break according to heuristic
			if (McsatVsSettings::BreakHeuristic(/*TODO break heuristic parameter (x, φ, α)*/))
			{
				break;
			}

			// generate region description
			FormulaT regiondesc = McsatVsSettings::RegionDescr(*currentVar, representative, mModel, symbolicZeros);
			regionDescriptions.push_back(std::move(regiondesc));

			// TODO substitution
			/*
				φ ← φ[t//x] ∧ sc (t)
			*/
		}

		// return final explanation
		FormulaT region = FormulaT(carl::FormulaType::AND, std::move(regionDescriptions));
		FormulaT formula = currentFormula;
		return smtrat::FormulaT(carl::FormulaType::IMPLIES, region, formula);
    }
	
	boost::optional<FormulaT> generateExplanation() const
	{
		// get test candidates from formula // TODO maybe only deal with constraints, not with conditions
		std::vector<vs::Condition> initialConditions;
		getConditionsFromConstraints(initialConditions, mConstraints);
		std::vector<vs::Condition*> conditions;
		// convert to vector of pointers:
		for (auto it = initialConditions.begin(); it != initialConditions.end(); ++it)
		{
			conditions.push_back(&(*it));
		}
		std::vector<vs::Substitution>& testCandidates;
		if (helper::generateTestCandidates(testCandidates, mTargetVar, conditions))
		{
			FormulasT res;
			for (auto tc = testCandidates.begin(); tc != testCandidates.end(); ++tc)
			{
				// TODO substitute

				FormulaT partial = generatePath(...); // TODO generate input to this call
				
				res.emplace_back(partial);
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

        return generateExplanation(); // TODO implement handling of arbitrary formulas in framework
	}
	
	
};

}
}
}
