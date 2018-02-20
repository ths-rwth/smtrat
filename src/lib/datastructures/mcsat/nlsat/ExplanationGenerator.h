#pragma once

#include "../../../Common.h"
#include "../../cad/projection/Projection.h"

#include <carl/util/Common.h>

namespace smtrat {
namespace mcsat {
namespace nlsat {

namespace helper {
	/**
	 * Construct a formula representing a variable comparison.
	 * If possible, this is simplified to a regular constraint.
	 */
	inline FormulaT buildFormulaFromVC(VariableComparisonT&& vc) {
		auto constraint = vc.asConstraint();
		if (constraint) {
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Simplified " << vc << " to " << *constraint);
			return FormulaT(*constraint);
		}
		return FormulaT(std::move(vc));
	}

	/**
	 * Construct a formula representing a variable being equal to the given multivariate root.
	 */
	template<typename MV>
	FormulaT buildEquality(carl::Variable v, const MV& mv) {
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "building: " << v << " = " << MultivariateRootT(mv.first, mv.second));
		return buildFormulaFromVC(VariableComparisonT(v, MultivariateRootT(mv.first, mv.second), carl::Relation::EQ));
	}
	/**
	 * Construct a formula representing a variable being less than the given multivariate root.
	 */
	template<typename MV>
	FormulaT buildBelow(carl::Variable v, const MV& mv) {
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "building: " << v << " < " << MultivariateRootT(mv.first, mv.second));
		return buildFormulaFromVC(VariableComparisonT(v, MultivariateRootT(mv.first, mv.second), carl::Relation::LESS));
	}
	/**
	 * Construct a formula representing a variable being greater than the given multivariate root.
	 */
	template<typename MV>
	FormulaT buildAbove(carl::Variable v, const MV& mv) {
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "building: " << v << " > " << MultivariateRootT(mv.first, mv.second));
		return buildFormulaFromVC(VariableComparisonT(v, MultivariateRootT(mv.first, mv.second), carl::Relation::GREATER));
	}
}

class ExplanationGenerator {
private:
	using RAN = carl::RealAlgebraicNumber<Rational>;
	struct ProjectionSettings: public cad::BaseSettings {	
		static constexpr cad::Incrementality incrementality = cad::Incrementality::NONE;
		static constexpr cad::Backtracking backtracking = cad::Backtracking::ORDERED;
		static constexpr cad::ProjectionType projectionOperator = cad::ProjectionType::Hong;
	};

	Model mModel;
	std::map<FormulaT, ConstraintT> mConstraints;
	cad::CADConstraints<ProjectionSettings::backtracking> mCADConstraints;
	cad::ModelBasedProjectionT<ProjectionSettings> mProjection;
	
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
				auto param = std::make_pair(Poly(carl::UnivariatePolynomial<Poly>(MultivariateRootT::var(), poly.coefficients())), rootID);
				SMTRAT_LOG_TRACE("smtrat.nlsat", root << " -> " << param);
				if (root < value) {
					if (!lower || (root > lower->first)) {
						lower = std::make_pair(root, helper::buildAbove(var, param));
						SMTRAT_LOG_TRACE("smtrat.nlsat", "new lower bound: " << lower->second);
					}
				} else if (root == value) {
					lower = std::make_pair(root, helper::buildEquality(var, param));
					upper = *lower;
					SMTRAT_LOG_TRACE("smtrat.nlsat", "new exact root: " << lower->second);
				} else {
					if (!upper || (root < upper->first)) {
						upper = std::make_pair(root, helper::buildBelow(var, param));
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
	ExplanationGenerator(const std::vector<FormulaT>& constraints, const std::vector<carl::Variable>& vars, carl::Variable targetVar, const Model& model):
		mModel(model),
		mConstraints(),
		mCADConstraints(
			[&](const auto& p, std::size_t cid, bool isBound){ mProjection.addPolynomial(mProjection.normalize(p), cid, isBound); },
			[&](const auto& p, std::size_t cid, bool isBound){ mProjection.removePolynomial(mProjection.normalize(p), cid, isBound); }
		),
		mProjection(mCADConstraints, mModel)
	{
		SMTRAT_LOG_TRACE("smtrat.nlsat", "Reset to " << vars);
		mCADConstraints.reset(vars);
		mProjection.reset();
		for (const auto& f: constraints) {
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding " << f << " to " << mConstraints);
			assert(mConstraints.find(f) == mConstraints.end());
			if (f.getType() == carl::FormulaType::CONSTRAINT) {
				SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding " << f);
				mConstraints.emplace(f, f.constraint());
			} else if (f.getType() == carl::FormulaType::VARCOMPARE) {
				SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding bound " << f);
				mConstraints.emplace(f, ConstraintT(f.variableComparison().definingPolynomial(), f.variableComparison().relation()));
			} else if (f.getType() == carl::FormulaType::VARASSIGN) {
				SMTRAT_LOG_WARN("smtrat.nlsat", "Variable assignment " << f << " should never get here!");
				assert(false);
				SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding assignment " << f);
				const VariableComparisonT& vc = f.variableAssignment();
				mConstraints.emplace(f, ConstraintT(vc.definingPolynomial(), carl::Relation::EQ));
			} else {
				SMTRAT_LOG_ERROR("smtrat.nlsat", "Unsupported formula type: " << f);
				assert(false);
			}
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "-> " << mConstraints);
		}
		std::set<ConstraintT> cons;
		for (const auto& c: mConstraints) {
			cons.insert(c.second);
		}
		for (const auto& c: cons) {
			mCADConstraints.add(c);
		}
		
		SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Starting with projection " << std::endl << mProjection);
		
		for (std::size_t level = 2; level < mCADConstraints.vars().size(); level++) {
			mProjection.projectNextLevel(level);
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "After projecting into level " << level << std::endl << mProjection);
		}

		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Projection is" << std::endl << mProjection);
	}

	void generateExplanation(const FormulaT& f, std::vector<FormulasT>& explanation) const {
		FormulasT subs;
		Model m;
		explanation.resize(mCADConstraints.vars().size());
		
		// Start from the bottom to generate bound constraints. 
		for (std::size_t level = mCADConstraints.vars().size() - 1; level > 0; level--) {
			carl::Variable var = mCADConstraints.vars()[level];
			if (mModel.find(var) == mModel.end()) continue;
			generateBoundsFor(explanation[level-1], var, level+1, m); 
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Cell bounds for " << var << ": " << explanation[level-1]);
			m.emplace(var, mModel.evaluated(var));
		}

		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Collecing constraints from " << mConstraints);
		for (const auto& c: mConstraints) {
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Considering " << c.first);
			if (c.first == f.negated()) {
				SMTRAT_LOG_DEBUG("smtrat.nlsat", "Skipping " << c.first);
				continue;
			}
			explanation.back().emplace_back(c.first);
		}
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Final: " << explanation.back() << " -> " << f);
	}
	
	FormulaT getExplanation(const FormulaT& f) const {
		std::vector<FormulasT> expl;
		generateExplanation(f, expl);
		FormulasT res;
		for (const auto& e: expl) {
			for (const auto& f: e) {
				//if (f.getType() == carl::FormulaType::VARCOMPARE) {
				//	res.emplace_back(f.variableComparison().invertRelation());
				//} else {
					res.emplace_back(f.negated());
				//}
			}
		}
		//std::cout << res << " => " << f << std::endl;
		if (!f.isTrue()) res.emplace_back(f);
		return FormulaT(carl::FormulaType::OR, std::move(res));
	}
};

}
}
}
