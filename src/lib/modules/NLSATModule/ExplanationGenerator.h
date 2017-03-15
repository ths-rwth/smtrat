#pragma once

#include "../../Common.h"
#include "../../datastructures/cad/projection/Projection.h"

#include <carl/util/Common.h>

namespace smtrat {

class ExplanationGenerator {
private:
	using RAN = carl::RealAlgebraicNumber<Rational>;
	struct ProjectionSettings: public cad::BaseSettings {	
		static constexpr cad::Incrementality incrementality = cad::Incrementality::NONE;
		static constexpr cad::Backtracking backtracking = cad::Backtracking::ORDERED;
	};

	std::vector<FormulaT> mConstraints;
	cad::CADConstraints<ProjectionSettings::backtracking> mCADConstraints;
	cad::ProjectionT<ProjectionSettings> mProjection;
	Model mModel;
	carl::Variable mTmpVar = carl::freshRealVariable("__z");
	
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
	FormulaT buildFormulaFromVC(VariableComparisonT&& vc) const {
		auto constraint = vc.asConstraint();
		if (constraint) return FormulaT(*constraint);
		else return FormulaT(std::move(vc));
	}
	template<typename MV>
	FormulaT buildEquality(carl::Variable v, const MV& mv) const {
		SMTRAT_LOG_TRACE("smtrat.nlsat", "building: " << v << " = " << MultivariateRootT(mv.first, mv.second, mTmpVar));
		return buildFormulaFromVC(VariableComparisonT(v, MultivariateRootT(mv.first, mv.second, mTmpVar), carl::Relation::EQ));
	}
	template<typename MV>
	FormulaT buildBelow(carl::Variable v, const MV& mv) const {
		SMTRAT_LOG_TRACE("smtrat.nlsat", "building: " << v << " < " << MultivariateRootT(mv.first, mv.second, mTmpVar));
		return buildFormulaFromVC(VariableComparisonT(v, MultivariateRootT(mv.first, mv.second, mTmpVar), carl::Relation::LESS));
	}
	template<typename MV>
	FormulaT buildAbove(carl::Variable v, const MV& mv) const {
		SMTRAT_LOG_TRACE("smtrat.nlsat", "building: " << v << " > " << MultivariateRootT(mv.first, mv.second, mTmpVar));
		return buildFormulaFromVC(VariableComparisonT(v, MultivariateRootT(mv.first, mv.second, mTmpVar), carl::Relation::GREATER));
	}
	
	void generateBoundsFor(FormulasT& res, carl::Variable var, std::size_t level, const Model& model) const {
		auto val = mModel.evaluated(var);
		assert(val.isRational() || val.isRAN());
		RAN value = val.isRational() ? RAN(val.asRational()) : val.asRAN();
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Generating bounds for " << var << " = " << value);
		boost::optional<std::pair<RAN,FormulaT>> lower;
		boost::optional<std::pair<RAN,FormulaT>> upper;

		for (std::size_t pid = 0; pid < mProjection.size(level); pid++) {
			const auto& poly = mProjection.getPolynomialById(level, pid);
			auto psubs = carl::model::substitute(poly, model);
			if (psubs.isZero()) continue;
			auto list = carl::model::realRoots(poly, model);
			if (!list) {
				// The polynomial vanished at this point
				continue;
			}
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Looking at " << poly << " with roots " << list);
			std::size_t rootID = 1;
			for (const auto& root: *list) {
				auto param = std::make_pair(Poly(carl::UnivariatePolynomial<Poly>(mTmpVar, poly.coefficients())), rootID);
				SMTRAT_LOG_TRACE("smtrat.nlsat", root << " -> " << param);
				if (root < value) {
					if (!lower || (root > lower->first)) {
						lower = std::make_pair(root, buildAbove(var, param));
						SMTRAT_LOG_TRACE("smtrat.nlsat", "new lower bound: " << lower->second);
					}
				} else if (root == value) {
					lower = std::make_pair(root, buildEquality(var, param));
					upper = lower;
					SMTRAT_LOG_TRACE("smtrat.nlsat", "new exact root: " << lower->second);
				} else {
					if (!upper || (root < upper->first)) {
						upper = std::make_pair(root, buildBelow(var, param));
						SMTRAT_LOG_TRACE("smtrat.nlsat", "new upper bound: " << upper->second);
					}
				}
				rootID++;
			}
		}
		if (lower) {
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Lower bound:" << lower->second);
			res.push_back(lower->second);
		}
		if (upper && lower != upper) {
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Upper bound:" << upper->second);
			res.push_back(upper->second);
		}
	}
public:
	ExplanationGenerator(const std::vector<FormulaT>& constraints, const std::vector<carl::Variable>& vars, const Model& model):
		mConstraints(constraints),
		mCADConstraints(
			[&](const auto& p, std::size_t cid, bool isBound){ mProjection.addPolynomial(mProjection.normalize(p), cid, isBound); },
			[&](const auto& p, std::size_t cid, bool isBound){ mProjection.removePolynomial(mProjection.normalize(p), cid, isBound); }
		),
		mProjection(mCADConstraints), 
		mModel(model)
	{
		SMTRAT_LOG_TRACE("smtrat.nlsat", "Reset to " << vars);
		mCADConstraints.reset(vars);
		mProjection.reset();
		for (const auto& f: mConstraints) {
			if (f.getType() == carl::FormulaType::CONSTRAINT) {
				SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding " << f);
				mCADConstraints.add(f.constraint());
			} else if (f.getType() == carl::FormulaType::VARCOMPARE) {
				SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding bound " << f);
			} else if (f.getType() == carl::FormulaType::VARASSIGN) {
				SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding assignment " << f);
			} else {
				SMTRAT_LOG_ERROR("smtrat.nlsat", "Unsupported formula type: " << f);
				assert(false);
			}
		}
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Projection is" << std::endl << mProjection);
	}
	void generateExplanation(const FormulaT& f, std::vector<FormulasT>& explanation) const {
		FormulasT subs;
		Model m;
		explanation.resize(mCADConstraints.vars().size());
		// Start from the bottom to incrementally build up model m and generate bound constraints.
		for (std::size_t level = mCADConstraints.vars().size() - 1; level > 0; level--) {
			carl::Variable var = mCADConstraints.vars()[level];
			generateBoundsFor(explanation[level-1], var, level+1, m);
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Cell bounds for " << var << ": " << explanation[level-1]);
			m.emplace(var, mModel.evaluated(var));
		}
		for (const auto& c: mConstraints) {
			if (c == f.negated()) continue;
			explanation.back().emplace_back(c);
		}
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Final: " << explanation.back() << " -> " << f);
	}

	template<typename Assignment, typename Callback>
	void generateAssignmentPropagationLemmas(const FormulasT& borders, const Assignment& assignment, const Callback& cb) {
		FormulasT base;
		for (const auto& ass: assignment) {
			for (const auto& sub: borders) {
				if (sub.variables().count(ass.first) > 0) {
					base.push_back(ass.second.negated());
				}
			}
		}
		for (const auto& b: borders) {
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding " << assignment << " -> " << b);
			auto tmp = base;
			tmp.push_back(b);
			FormulaT f(carl::FormulaType::OR, std::move(tmp));
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Actual: " << f);
			cb(f);
		}
	}
	template<typename Assignment, typename Callback>
	void generateMainPropagationLemma(const std::vector<FormulasT>& explanation, const FormulaT& F, const Assignment& assignment, const Callback& cb) {
		FormulasT E;
		for (const auto& expl: explanation) {
			E.insert(E.end(), expl.begin(), expl.end());
		}
		for (const auto& ass: assignment) {
			for (const auto& expl: explanation) {
				for (const auto& e: expl) {
					if (e.variables().count(ass.first) > 0) {
						E.push_back(ass.second);
					}
				}
			}
		}
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding " << E << " -> " << F);
		for (auto& e: E) e = e.negated();
		E.push_back(F);
		cb(FormulaT(carl::FormulaType::OR, std::move(E)));
	}
	
	template<typename Assignment, typename Callback>
	void generateExplanationLemmas(const FormulaT& F, const Assignment& assignment, const Callback& cb) {
		std::vector<FormulasT> explanation;
		generateExplanation(F, explanation);
		
		for (const auto& expl: explanation) {
			if (expl.empty()) continue;
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Processing borders: " << expl);
			generateAssignmentPropagationLemmas(expl, assignment, cb);
		}
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Using " << F.negated() << " for R-propagation");
		generateMainPropagationLemma(explanation, F.negated(), assignment, cb);
	}
};

}
