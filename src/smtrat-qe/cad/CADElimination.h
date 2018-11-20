#pragma once

#include "../QEQuery.h"

#include <lib/datastructures/cad/Settings.h>
#include <lib/datastructures/cad/helper/CADCore.h>
#include <lib/datastructures/cad/lifting/LiftingTree.h>
#include <lib/datastructures/cad/lifting/Sample.h>
#include <lib/datastructures/cad/projection/Projection.h>
#include "CAD.h"

#include <carl/core/MultivariatePolynomial.h>
#include <carl/core/Relation.h>
#include <carl/core/Sign.h>
#include <carl/core/UnivariatePolynomial.h>
#include <carl/core/polynomialfunctions/Factorization.h>
#include <carl/formula/model/Model.h>
#include <carl/formula/model/ran/RealAlgebraicNumberEvaluation.h>

#include <algorithm>
#include <iostream>
#include <map>
#include <string>
#include <utility>
#include <vector>

namespace smtrat::qe::cad {

struct CADSettings : smtrat::cad::BaseSettings {
	static constexpr smtrat::cad::ProjectionType projectionOperator = smtrat::cad::ProjectionType::Brown;
	static constexpr smtrat::cad::Incrementality incrementality = smtrat::cad::Incrementality::NONE;
	static constexpr smtrat::cad::Backtracking backtracking = smtrat::cad::Backtracking::UNORDERED;
};

class CADElimination {
private:
	FormulaT mQuantifierFreePart;
	std::vector<carl::Variable> mVariables;
	std::vector<ConstraintT> mConstraints;
	std::vector<std::pair<QuantifierType, carl::Variable>> mQuantifiers;

	std::size_t n;
	std::size_t k;

	CAD<CADSettings> mCAD;

	using TreeIT = CAD<CADSettings>::TreeIterator;

	std::map<TreeIT, bool> mTruth;
	std::map<TreeIT, std::vector<carl::Sign>> mSignature;

	std::vector<std::pair<TreeIT, TreeIT>> mCauseConflict;

	std::vector<TreeIT> mTrueSamples;
	std::vector<TreeIT> mFalseSamples;
	FormulasT mAtomicFormulas;

	auto& tree() {
		return mCAD.getLifting().getTree();
	}
	const auto& tree() const {
		return mCAD.getLifting().getTree();
	}

	std::vector<TreeIT> collectChildren(const TreeIT& it) const {
		std::vector<TreeIT> res;
		for (auto child = tree().begin_children(it); child != tree().end_children(it); ++child) {
			res.emplace_back(child);
		}
		return res;
	}

	void constructCAD();
	void updateCAD(std::vector<Poly>& polynomials);

	void simplifyCAD();
	bool truthBoundaryTest(TreeIT& b, TreeIT& c, TreeIT& d);

	void computeTruthValues();
	void computeSignatures();

	bool isProjectionDefinable();
	void makeProjectionDefinable();

	FormulaT constructImplicant(const TreeIT& sample);
	FormulaT constructSolutionFormula();

	template<typename T>
	std::vector<T> computeHittingSet(const std::vector<std::vector<T>>& setOfSets);

public:
	CADElimination(const FormulaT& quantifierFreePart, const QEQuery& quantifiers);
	FormulaT eliminateQuantifiers();
};

} // namespace smtrat::qe::cad
