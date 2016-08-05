#pragma once

#include "../Common.h"

#include "cad/projection/Projection.h"

#include <carl/util/Common.h>

namespace smtrat {

class ExplanationGenerator {
private:
	using RAN = carl::RealAlgebraicNumber<Rational>;
	struct ProjectionSettings: public cad::BaseSettings {	
		static constexpr cad::Incrementality incrementality = cad::Incrementality::NONE;
		static constexpr cad::Backtracking backtracking = cad::Backtracking::ORDERED;
	};
	
	std::vector<ConstraintT> mConstraints;
	cad::CADConstraints<ProjectionSettings::backtracking> mCADConstraints;
	cad::ProjectionT<ProjectionSettings> mProjection;
	Model mModel;
	carl::Variable mTmpVar = carl::freshRealVariable("_z");
	
	bool isEqual(const RAN& ran, const ModelValue& mv) const {
		if (mv.isRational()) return ran == RAN(mv.asRational());
		if (mv.isRAN()) return ran == mv.asRAN();
		assert(false);
		return false;
	}
	bool isGreater(const RAN& ran, const ModelValue& mv) const {
		if (mv.isRational()) return ran > RAN(mv.asRational());
		if (mv.isRAN()) return ran > mv.asRAN();
		assert(false);
		return false;
	}
	template<typename MV>
	FormulaT buildEquality(carl::Variable v, const MV& mv) const {
		return FormulaT(VariableComparisonT(v, MultivariateRootT(mv.first, mv.second, mTmpVar), carl::Relation::NEQ));
	}
	template<typename MV>
	FormulaT buildBelow(carl::Variable v, const MV& right) const {
		return FormulaT(VariableComparisonT(v, MultivariateRootT(right.first, right.second, mTmpVar), carl::Relation::GEQ));
	}
	template<typename MV>
	FormulaT buildBetween(carl::Variable v, const MV& left, const MV& right) const {
		return FormulaT(carl::FormulaType::OR, buildAbove(v, left), buildBelow(v, right));
	}
	template<typename MV>
	FormulaT buildAbove(carl::Variable v, const MV& left) const {
		return FormulaT(VariableComparisonT(v, MultivariateRootT(left.first, left.second, mTmpVar), carl::Relation::LEQ));
	}
	
	FormulaT generateBoundsFor(carl::Variable var, std::size_t level, const Model& model) {
		std::map<RAN, std::pair<Poly, std::size_t>> roots;
		for (std::size_t pid = 0; pid < mProjection.size(level); pid++) {
			const auto& poly = mProjection.getPolynomialById(level, pid);
			auto list = carl::model::realRoots(poly, model);
			std::size_t rootID = 1;
			for (const auto& root: list) {
				roots.emplace(root, std::make_pair(carl::UnivariatePolynomial<Poly>(mTmpVar, poly.coefficients()), rootID));
				rootID++;
			}
		}
		auto val = mModel.evaluated(var);
		assert(val.isRational() || val.isRAN());
		for (auto it = roots.begin(); it != roots.end(); it++) {
			if (isEqual(it->first, val)) {
				return buildEquality(var, it->second);
			}
			if (isGreater(it->first, val)) {
				if (it == roots.begin()) {
					return buildBelow(var, it->second);
				} else {
					return buildBetween(var, std::next(it, -1)->second, it->second);
				}
			}
		}
		if (roots.empty()) {
			assert(false);
		}
		return buildAbove(var, roots.rbegin()->second);
	}
public:
	ExplanationGenerator(const std::vector<ConstraintT>& constraints, const std::vector<carl::Variable>& vars, const Model& model):
		mConstraints(constraints),
		mCADConstraints(
			[&](const auto& p, std::size_t cid, bool isBound){ mProjection.addPolynomial(mProjection.normalize(p), cid, isBound); },
			[&](const auto& p, std::size_t cid, bool isBound){ mProjection.removePolynomial(mProjection.normalize(p), cid, isBound); }
		),
		mProjection(mCADConstraints), 
		mModel(model)
	{
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Reset to " << vars);
		mCADConstraints.reset(vars);
		mProjection.reset();
		for (const auto& c: mConstraints) {
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding " << c);
			mCADConstraints.add(c);
		}
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Projection is" << std::endl << mProjection);
	}
	FormulaT generateExplanation(const ConstraintT& reason) {
		FormulasT subs;
		Model m;
		for (std::size_t level = mCADConstraints.vars().size()-1; level > 0; level--) {
			carl::Variable var = mCADConstraints.vars()[level];
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Explanation for " << var);
			subs.emplace_back(generateBoundsFor(var, level+1, m));
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "-> " << subs.back());
			m.emplace(var, mModel.evaluated(var));
		}
		subs.emplace_back(ConstraintT(reason.lhs(), inverse(reason.relation())));
		return FormulaT(carl::FormulaType::OR, std::move(subs));
	}
};

}
