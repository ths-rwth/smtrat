#include "CADElimination.h"

#include <sstream>

namespace smtrat {
namespace qe {
namespace cad {

using smtrat::cad::Assignment;
using smtrat::cad::RAN;

CADElimination::CADElimination(const FormulaT& quantifierFreePart, const QEQuery& quantifiers) {
	mQuantifierFreePart = quantifierFreePart;
	mQuantifiers = smtrat::qe::flattenQEQuery(quantifiers);

	carl::carlVariables vars;
	quantifierFreePart.gatherVariables(vars);
	// quantified variables
	for (const auto& v : mQuantifiers) {
		mVariables.emplace_back(v.second);
		vars.erase(v.second);
	}
	for (auto v : vars) {
		mVariables.emplace_back(v);
	}

	// number of variables
	n = mVariables.size();
	// number of free variables
	k = mVariables.size() - mQuantifiers.size();

	mQuantifierFreePart.getConstraints(mConstraints);
}

FormulaT CADElimination::eliminateQuantifiers() {
	constructCAD();

	computeTruthValues();

	simplifyCAD();

	if (!isProjectionDefinable()) {
		SMTRAT_LOG_DEBUG("smtrat.qe", "The CAD is not projection-definable");
		makeProjectionDefinable();
	} else {
		SMTRAT_LOG_DEBUG("smtrat.qe", "The CAD is already projection-definable");
	}

	return constructSolutionFormula();
}

void CADElimination::constructCAD() {
	mCAD.reset(mVariables);

	for (const auto& c : mConstraints) {
		mCAD.addPolynomial(c.lhs());
	}

	mCAD.project();
	mCAD.lift();
}

void CADElimination::updateCAD(std::vector<Poly>& polynomials) {
	// polynomials with lowest degree will be added first
	std::sort(polynomials.begin(), polynomials.end());

	for (const auto& p : polynomials) {
		mCAD.addPolynomial(p);

		mCAD.project();
		mCAD.lift();

		if (isProjectionDefinable()) {
			break;
		}
	}

	computeTruthValues();
}

void CADElimination::simplifyCAD() {
	std::vector<TreeIT> truthBoundaryCells;

	// level k
	for (auto it = tree().begin_depth(k); it != tree().end_depth(); it++) {
		if (it->isRoot()) {
			TreeIT c = it;
			TreeIT b = it.previous();
			TreeIT d = it.next().next();

			if (mTruth.find(b)->second != mTruth.find(c)->second || mTruth.find(c)->second != mTruth.find(d)->second) {
				SMTRAT_LOG_DEBUG("smtrat.qe", mCAD.getLifting().extractSampleMap(c) << " is a truth-boundary cell");
				truthBoundaryCells.push_back(c);
			}
		}
	}
	std::vector<std::vector<Poly>> S;
	for (const auto& cell : truthBoundaryCells) {
		std::vector<Poly> P;
		std::size_t numberOfProjectionFactors = mCAD.getProjection().size(n + 1 - k);
		for (std::size_t id = 0; id < numberOfProjectionFactors; id++) {
			if (mCAD.getProjection().hasPolynomialById(n + 1 - k, id)) {
				Poly p(mCAD.getProjection().getPolynomialById(n + 1 - k, id));
				if (carl::Sign::ZERO == carl::sgn(carl::evaluate(p, mCAD.getLifting().extractSampleMap(cell)))) {
					P.push_back(p);
				}
			}
		}
		if (!P.empty()) {
			S.push_back(P);
		}
	}
	if (!S.empty()) {
		std::vector<Poly> H = computeHittingSet(S);
		std::size_t numberOfProjectionFactors = mCAD.getProjection().size(n + 1 - k);
		for (std::size_t id = 0; id < numberOfProjectionFactors; id++) {
			if (mCAD.getProjection().hasPolynomialById(n + 1 - k, id)) {
				Poly p(mCAD.getProjection().getPolynomialById(n + 1 - k, id));
				if (std::find(H.begin(), H.end(), p) == H.end()) {
					SMTRAT_LOG_DEBUG("smtrat.qe", "Remove " << p);
					mCAD.removePolynomial(n + 1 - k, id);
				}
			}
		}
		H.clear();
	}
	computeTruthValues();

	// level k-1 and below
	truthBoundaryCells.clear();
	S.clear();

	if (k > 0) {
		for (std::size_t i = k - 1; i > 0; i--) {
			std::vector<Poly> N;
			std::size_t numberOfProjectionFactors = mCAD.getProjection().size(n + 1 - i);
			for (std::size_t id = 0; id < numberOfProjectionFactors; id++) {
				if (mCAD.getProjection().hasPolynomialById(n + 1 - i, id)) {
					if (mCAD.getProjection().testProjectionFactor(n + 1 - i, id)) {
						N.emplace_back(mCAD.getProjection().getPolynomialById(n + 1 - i, id));
					}
				}
			}
			for (auto it = tree().begin_depth(i); it != tree().end_depth(); it++) {
				if (it->isRoot()) {
					TreeIT c = it;
					TreeIT b = it.previous();
					TreeIT d = it.next().next();
					if (truthBoundaryTest(b, c, d)) {
						SMTRAT_LOG_DEBUG("smtrat.qe", mCAD.getLifting().extractSampleMap(c) << " is a truth-boundary cell");
						truthBoundaryCells.push_back(c);
					}
				}
			}
			for (const auto& cell : truthBoundaryCells) {
				std::vector<Poly> P;
				for (std::size_t id = 0; id < numberOfProjectionFactors; id++) {
					if (mCAD.getProjection().hasPolynomialById(n + 1 - i, id)) {
						Poly p(mCAD.getProjection().getPolynomialById(n + 1 - i, id));
						if (carl::Sign::ZERO == carl::sgn(carl::evaluate(p, mCAD.getLifting().extractSampleMap(cell)))) {
							P.push_back(p);
						}
					}
				}
				if (!P.empty()) {
					S.push_back(P);
				}
			}
			if (!S.empty()) {
				std::vector<Poly> H = computeHittingSet(S);
				for (std::size_t id = 0; id < numberOfProjectionFactors; id++) {
					if (mCAD.getProjection().hasPolynomialById(n + 1 - i, id)) {
						Poly p(mCAD.getProjection().getPolynomialById(n + 1 - i, id));
						if (std::find(N.begin(), N.end(), p) == N.end() && std::find(H.begin(), H.end(), p) == H.end()) {
							SMTRAT_LOG_DEBUG("smtrat.qe", "Remove " << p);
							mCAD.removePolynomial(n + 1 - i, id);
						}
					}
				}
				H.clear();
			}
			truthBoundaryCells.clear();
			S.clear();
		}
	} else {
		SMTRAT_LOG_DEBUG("smtrat.qe", "Can not simplify CAD further, as there are no free variables.");
	}
	computeTruthValues();
}

bool CADElimination::truthBoundaryTest(TreeIT& b, TreeIT& c, TreeIT& d) {
	std::vector<TreeIT> children_b = collectChildren(b);
	std::vector<TreeIT> children_c = collectChildren(c);
	std::vector<TreeIT> children_d = collectChildren(d);

	if (tree().max_depth(c) == k - 1) {
		if (children_b.size() == children_c.size() && children_c.size() == children_d.size()) {
			for (std::size_t i = 0; i < children_c.size(); i++) {
				if (mTruth.find(children_b[i])->second != mTruth.find(children_c[i])->second || mTruth.find(children_c[i])->second != mTruth.find(std::next(children_d[i]))->second) {
					return true;
				}
			}
		}
	} else {
		if (children_b.size() == children_c.size() && children_c.size() == children_d.size()) {
			for (std::size_t i = 0; i < children_c.size(); i++) {
				if (truthBoundaryTest(children_b[i], children_c[i], children_d[i])) {
					return true;
				}
			}
		}
	}
	return false;
}

void CADElimination::computeTruthValues() {
	mTruth.clear();

	// level n
	for (auto it = tree().begin_leaf(); it != tree().end_leaf(); it++) {
		Assignment assignment = mCAD.getLifting().extractSampleMap(it);
		Model model;
		for (const auto& a : assignment) {
			model.emplace(a.first, a.second);
		}
		bool truthValue = carl::model::evaluate(mQuantifierFreePart, model).asBool();
		mTruth.emplace(it, truthValue);
	}

	// level n-1 down to level k
	std::size_t i = n - 1;
	for (auto quantifier = mQuantifiers.rbegin(); quantifier != mQuantifiers.rend(); quantifier++) {
		for (auto it = tree().begin_depth(i); it != tree().end_depth(); it++) {
			if (quantifier->first == QuantifierType::EXISTS) {
				bool truthValue = false;
				for (auto child = tree().begin_children(it); child != tree().end_children(it); child++) {
					truthValue = truthValue || mTruth.find(child)->second;
				}
				mTruth.emplace(it, truthValue);
			}
			if (quantifier->first == QuantifierType::FORALL) {
				bool truthValue = true;
				for (auto child = tree().begin_children(it); child != tree().end_children(it); child++) {
					truthValue = truthValue && mTruth.find(child)->second;
				}
				mTruth.emplace(it, truthValue);
			}
		}
		i = i - 1;
	}
}

void CADElimination::computeSignatures() {
	mSignature.clear();

	Assignment assignment;
	std::vector<carl::Sign> signature;
	for (auto it = tree().begin_depth(k); it != tree().end_depth(); it++) {
		assignment = mCAD.getLifting().extractSampleMap(it);
		Model model;
		for (const auto& a : assignment) {
			model.emplace(a.first, a.second);
		}
		for (std::size_t i = 1; i <= k; i++) {
			std::size_t numberOfProjectionFactors = mCAD.getProjection().size(n + 1 - i);
			for (std::size_t id = 0; id < numberOfProjectionFactors; id++) {
				if (mCAD.getProjection().hasPolynomialById(n + 1 - i, id)) {
					signature.push_back(carl::sgn(carl::evaluate(Poly(mCAD.getProjection().getPolynomialById(n + 1 - i, id)), assignment)));
				}
			}
		}
		mSignature.emplace(it, signature);

		assignment.clear();
		signature.clear();
	}
}

// helper to swap the keys and values of a map
template<typename key, typename value>
std::multimap<value, key> flip_map(const std::map<key, value>& src) {
	std::multimap<value, key> dst;
	for (const auto& s: src) {
		dst.emplace(s.second, s.first);
	}
	return dst;
}

bool CADElimination::isProjectionDefinable() {
	mCauseConflict.clear();

	bool projectionDefinable = true;
	std::vector<TreeIT> samplesOfSameSignature;

	computeSignatures();
	std::multimap<std::vector<carl::Sign>, TreeIT> signature_flipped = flip_map(mSignature);
	std::vector<carl::Sign> signature = signature_flipped.begin()->first;

	for (const auto& s : signature_flipped) {
		if (signature == s.first) {
			samplesOfSameSignature.push_back(s.second);
		} else {
			for (auto a = samplesOfSameSignature.begin(); a != samplesOfSameSignature.end(); a++) {
				for (auto b = std::next(a); b != samplesOfSameSignature.end(); b++) {
					if (mTruth.find(*a)->second != mTruth.find(*b)->second) {
						mCauseConflict.push_back(std::make_pair(*a, *b));
						projectionDefinable = false;
					}
				}
			}
			samplesOfSameSignature.clear();
			samplesOfSameSignature.push_back(s.second);

			signature.clear();
			signature = s.first;
		}
	}
	return projectionDefinable;
}

void CADElimination::makeProjectionDefinable() {
	for (std::size_t i = k; i >= 1; i--) {
		std::vector<std::pair<TreeIT, TreeIT>> conflictingPairs;
		for (const auto& pair : mCauseConflict) {
			TreeIT a = pair.first;
			TreeIT b = pair.second;
			bool equals = false;
			for (std::size_t level = k; level > i; level--) {
				a = tree().get_parent(a);
				b = tree().get_parent(b);
				if (a == b) {
					equals = true;
				}
			}
			if (!equals) {
				if (tree().get_parent(a) == tree().get_parent(b)) {
					if (*a < *b) {
						conflictingPairs.push_back(std::make_pair(a, b));
					} else {
						conflictingPairs.push_back(std::make_pair(b, a));
					}
				}
			}
		}

		std::vector<carl::UnivariatePolynomial<Poly>> setOfProjectionFactors;
		std::vector<std::vector<carl::UnivariatePolynomial<Poly>>> setOfSetOfProjectionFactors;
		for (const auto& conflictingPair : conflictingPairs) {
			std::size_t numberOfProjectionFactors = mCAD.getProjection().size(n + 1 - i);
			for (std::size_t id = 0; id < numberOfProjectionFactors; id++) {
				if (mCAD.getProjection().hasPolynomialById(n + 1 - i, id)) {
					bool zeroInSomeCell = false, vanish = true;
					carl::UnivariatePolynomial<Poly> projectionFactor = mCAD.getProjection().getPolynomialById(n + 1 - i, id);
					TreeIT it = conflictingPair.second;
					while (*conflictingPair.first < *it) {
						if (carl::Sign::ZERO == carl::sgn(carl::evaluate(Poly(projectionFactor), mCAD.getLifting().extractSampleMap(it)))) {
							zeroInSomeCell = true;
						} else {
							vanish = false;
						}
						it = tree().left_sibling(it);
					}
					if (vanish) {
						for (auto child = tree().begin_children(tree().get_parent(conflictingPair.first)); child != tree().end_children(tree().get_parent(conflictingPair.first)); child++) {
							if (carl::Sign::ZERO != carl::sgn(carl::evaluate(Poly(projectionFactor), mCAD.getLifting().extractSampleMap(child)))) {
								vanish = false;
							}
						}
					}
					if (zeroInSomeCell && !vanish) {
						setOfProjectionFactors.push_back(projectionFactor);
					}
				}
			}
			if (setOfProjectionFactors.size() != 0) {
				setOfSetOfProjectionFactors.push_back(setOfProjectionFactors);
				setOfProjectionFactors.clear();
			}
		}
		std::vector<carl::UnivariatePolynomial<Poly>> hittingSet = computeHittingSet(setOfSetOfProjectionFactors);

		std::vector<Poly> addToCAD;
		for (const auto& p : hittingSet) {
			for (uint nth = 0; nth <= p.degree(); nth++) {
				Poly nthDerivative(carl::derivative(p, nth));
				auto factorizationOfTheDerivative = carl::factorization(nthDerivative, false);

				for (const auto& factor : factorizationOfTheDerivative) {
					addToCAD.push_back(factor.first);
				}
			}
		}

		for (const auto& p : addToCAD) {
			SMTRAT_LOG_DEBUG("smtrat.qe", "Add " << p);
		}

		updateCAD(addToCAD);

		// if projection-definability is already achieved, we are done
		if (isProjectionDefinable()) {
			SMTRAT_LOG_DEBUG("smtrat.qe", "The CAD is now projection-definable");
			break;
		} else {
			SMTRAT_LOG_DEBUG("smtrat.qe", "The CAD is still not projection-definable");
		}
	}
}

FormulaT CADElimination::constructImplicant(const TreeIT& sample) {
	Assignment assignment;
	Model model;
	assignment = mCAD.getLifting().extractSampleMap(sample);
	for (const auto& a : assignment) {
		model.emplace(a.first, a.second);
	}
	FormulasT L;
	for (const auto& atomicFormula : mAtomicFormulas) {
		if (carl::model::evaluate(atomicFormula, model).asBool()) {
			L.push_back(atomicFormula);
		}
	}

	assignment.clear();
	model.clear();
	FormulasT evaluatedToFalse;
	std::vector<FormulasT> S;
	for (const auto& falseSample : mFalseSamples) {
		assignment = mCAD.getLifting().extractSampleMap(falseSample);
		for (const auto& a : assignment) {
			model.emplace(a.first, a.second);
		}
		for (const auto& atomicFormula : L) {
			if (!carl::model::evaluate(atomicFormula, model).asBool()) {
				evaluatedToFalse.push_back(atomicFormula);
			}
		}
		assignment.clear();
		model.clear();
		if (!evaluatedToFalse.empty()) {
			S.push_back(evaluatedToFalse);
			evaluatedToFalse.clear();
		}
	}

	FormulasT H = computeHittingSet(S);
	SMTRAT_LOG_DEBUG("smtrat.qe", FormulaT(carl::FormulaType::AND, H) << " is an implicant capturing " << mCAD.getLifting().extractSampleMap(sample));
	return FormulaT(carl::FormulaType::AND, H);
}

FormulaT CADElimination::constructSolutionFormula() {
	for (auto sample_iterator = tree().begin_depth(k); sample_iterator != tree().end_depth(); sample_iterator++) {
		if (mTruth.find(sample_iterator)->second) {
			mTrueSamples.push_back(sample_iterator);
		} else {
			mFalseSamples.push_back(sample_iterator);
		}
	}
	for (std::size_t level = 1; level <= k; level++) {
		std::size_t numberOfProjectionFactors = mCAD.getProjection().size(n + 1 - level);
		for (std::size_t id = 0; id < numberOfProjectionFactors; id++) {
			if (mCAD.getProjection().hasPolynomialById(n + 1 - level, id)) {
				Poly p(mCAD.getProjection().getPolynomialById(n + 1 - level, id));
				mAtomicFormulas.emplace_back(ConstraintT(p, carl::Relation::EQ));
				mAtomicFormulas.emplace_back(ConstraintT(p, carl::Relation::NEQ));
				mAtomicFormulas.emplace_back(ConstraintT(p, carl::Relation::LESS));
				mAtomicFormulas.emplace_back(ConstraintT(p, carl::Relation::LEQ));
				mAtomicFormulas.emplace_back(ConstraintT(p, carl::Relation::GREATER));
				mAtomicFormulas.emplace_back(ConstraintT(p, carl::Relation::GEQ));
			}
		}
	}

	FormulasT implicants;
	bool captured = false;
	for (auto const& sample : mTrueSamples) {
		Assignment assignment = mCAD.getLifting().extractSampleMap(sample);
		Model model;
		for (const auto& a : assignment) {
			model.emplace(a.first, a.second);
		}
		for (auto const& implicant : implicants) {
			if (carl::model::evaluate(implicant, model).asBool()) {
				captured = true;
			}
		}
		if (!captured) {
			FormulaT implicant = constructImplicant(sample);
			implicants.push_back(implicant);
		}
		captured = false;
	}

	FormulasT i;
	std::vector<FormulasT> I;
	for (auto const& sample : mTrueSamples) {
		Assignment assignment = mCAD.getLifting().extractSampleMap(sample);
		Model model;
		for (const auto& a : assignment) {
			model.emplace(a.first, a.second);
		}
		for (auto const& implicant : implicants) {
			if (carl::model::evaluate(implicant, model).asBool()) {
				i.push_back(implicant);
			}
		}
		if (!i.empty()) {
			I.push_back(i);
			i.clear();
		}
	}

	FormulasT H = computeHittingSet(I);
	return FormulaT(carl::FormulaType::OR, H);
}

template<typename T>
std::vector<T> CADElimination::computeHittingSet(const std::vector<std::vector<T>>& setOfSets) {
	std::vector<std::vector<T>> SoS(setOfSets);

	std::vector<T> H;
	std::map<T, int> U;

	for (const auto& set : SoS) {
		for (const auto& element : set) {
			if (U.find(element) != U.end()) {
				U.find(element)->second++;
			} else {
				U.emplace(element, 1);
			}
		}
	}

	while (!SoS.empty()) {
		auto max = U.begin();
		for (auto it = U.begin(); it != U.end(); it++) {
			if (it->second > max->second) {
				max = it;
			}
		}
		H.push_back(max->first);
		for (auto set = SoS.begin(); set != SoS.end();) {
			if (std::find(set->begin(), set->end(), max->first) != set->end()) {
				set = SoS.erase(set);
			} else {
				++set;
			}
		}
		U.erase(max);
		if (!U.empty()) {
			for (auto it = U.begin(); it != U.end(); it++) {
				it->second = 0;
			}
			for (const auto& set : SoS) {
				for (const auto& element : set) {
					if (U.find(element) != U.end()) {
						U.find(element)->second++;
					}
				}
			}
		}
	}

	return H;
}

} // namespace cad
} // namespace qe
} // namespace smtrat
