#include "ExactlyOneCommanderEncoder.h"

namespace smtrat {

	// https://github.com/Z3Prover/z3/issues/755 show experiments which state that a group size of 4 is optimal.
	static constexpr int COMMANDER_GROUP_SIZE = 4;

	Rational ExactlyOneCommanderEncoder::encodingSize(const ConstraintT& constraint) {
		if (!canEncode(constraint)) return PseudoBoolEncoder::encodingSize(constraint);

		// groups * (vars * (vars + 1)/2) + 1
		size_t nVars = constraint.variables().size();

		return 4 * (nVars * (nVars + 1))/2 + 1;
	}

	bool ExactlyOneCommanderEncoder::canEncode(const ConstraintT& constraint) {
		if (constraint.relation() != carl::Relation::EQ) return false;
		if (constraint.variables().size() <= COMMANDER_GROUP_SIZE) return false;

		for (const auto &term : constraint.lhs()) {
			if (term.is_constant()) continue;

			if (term.coeff() != Rational(1)) {
				return false;
			}
		}

		return constraint.lhs().constant_part() == Rational(-1);
	}

	std::optional<FormulaT> ExactlyOneCommanderEncoder::doEncode(const ConstraintT& constraint) {
		assert(canEncode(constraint));

		// 1. partition into groups of (mostly) equal size and introduce a group commander variable (bool)
		std::map<carl::Variable, std::vector<carl::Variable>> commanderPartitions = partition(constraint.variables().as_set());

		FormulasT result;
		std::vector<carl::Variable> commanders;
		for (const auto& entry : commanderPartitions) {
			carl::Variable commander = entry.first;
			commanders.push_back(commander);
			std::vector<carl::Variable> group = entry.second;

			// 2. atmost one variable in the group is true
			for (size_t i = 0; i < group.size(); i++) {
				for (size_t j = 0; j < i; j++) {
					// group_i -> not group_j
					result.push_back(FormulaT(carl::FormulaType::OR, !FormulaT(group[i]), !FormulaT(group[j])));
				}
			}

			carl::Variables groupVarSet(group.begin(), group.end());
			// 3. group commander implies atleast 1 of the group true
			result.push_back(FormulaT(carl::FormulaType::OR, !FormulaT(commander), generateVarChain(groupVarSet, carl::FormulaType::OR)));

			// 4. not group commander implies none true
			for (size_t i = 0; i < group.size(); i++) {
				result.push_back(FormulaT(carl::FormulaType::OR, FormulaT(commander), !FormulaT(group[i])));
			}
		}

		// 5. exactly one commander true (recursively or directly via existing encoding)
		Poly commanderConstraintPoly;
		commanderConstraintPoly += Rational(-1);
		for (const auto& cmdVar : commanders) {
			commanderConstraintPoly += Poly(cmdVar);
		}

		ConstraintT commanderConstraint(commanderConstraintPoly, carl::Relation::EQ);
		result.push_back(*mCardinalityEncoder.encode(commanderConstraint));

		return FormulaT(carl::FormulaType::AND, result);
	}

	std::map<carl::Variable, std::vector<carl::Variable>> ExactlyOneCommanderEncoder::partition(carl::Variables vars) {
		std::map<carl::Variable, std::vector<carl::Variable>> result;

		std::vector<carl::Variable> varVector;
		std::copy(vars.begin(), vars.end(), std::back_inserter(varVector));

		// initialize result map
		std::vector<carl::Variable> commanders;
		for (int i = 0; i < COMMANDER_GROUP_SIZE; i++) {
			carl::Variable commander = carl::fresh_boolean_variable();
			commanders.push_back(commander);
			result[commander] = std::vector<carl::Variable>();
		}

		// fill result map
		for (size_t i = 0; i < varVector.size(); i++) {
			carl::Variable commander = commanders[i % COMMANDER_GROUP_SIZE];
			result[commander].push_back(varVector[i]);
		}

		return result;

	}

}
