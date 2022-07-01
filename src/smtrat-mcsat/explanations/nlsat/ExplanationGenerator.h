#pragma once


#include <smtrat-cad/projection/Projection.h>
#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>

#include <carl-arith/core/Common.h>

namespace smtrat {
namespace mcsat {
namespace nlsat {

namespace helper {
	/**
	 * Construct a formula representing a variable comparison.
	 * Simplify to a regular constraint if possible.
	 */
	inline FormulaT buildFormulaFromVC(VariableComparisonT&& vc) {
		auto constraint = carl::as_constraint(vc);
		if (constraint) {
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Simplified " << vc << " to " << *constraint);
			return FormulaT(ConstraintT(*constraint));
		}
		return FormulaT(std::move(vc));
	}

	/**
	 * Construct an atomic formula representing a variable being equal to the given multivariate root. "v = root(..)"
	 */
	template<typename MVRootParams>
	FormulaT buildEquality(carl::Variable var, const MVRootParams& mvp) {
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "building: " << var << " = " << MultivariateRootT(mvp.first, mvp.second, var));
		return buildFormulaFromVC(VariableComparisonT(var, MultivariateRootT(mvp.first, mvp.second, var), carl::Relation::EQ));
	}
	/**
	 * Construct an atomic formula representing a variable being less than the given multivariate root. "v < root(..)"
	 */
	template<typename MVRootParams>
	FormulaT buildBelow(carl::Variable var, const MVRootParams& mvp) {
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "building: " << var << " < " << MultivariateRootT(mvp.first, mvp.second, var));
		return buildFormulaFromVC(VariableComparisonT(var, MultivariateRootT(mvp.first, mvp.second, var), carl::Relation::LESS));
	}
	/**
	 * Construct an atomic formula representing a variable being greater than the given multivariate root. "v > root(..)"
	 */
	template<typename MVRootParams>
	FormulaT buildAbove(carl::Variable var, const MVRootParams& mvp) {
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "building: " << var << " > " << MultivariateRootT(mvp.first, mvp.second, var));
		return buildFormulaFromVC(VariableComparisonT(var, MultivariateRootT(mvp.first, mvp.second, var), carl::Relation::GREATER));
	}

	/**
	 * Transform constraints represented as atomic formualas into the easier to
	 * use objects of the Constraint class.
	 */
	inline
	std::set<ConstraintT> convertToConstraints(std::vector<FormulaT> constraintAtoms) {
		std::set<ConstraintT> cons;
		for (const auto& cAtom: constraintAtoms) {
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding " << cAtom << " to " << cons);
			if (cAtom.type() == carl::FormulaType::CONSTRAINT) {
				SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding " << cAtom);
				cons.emplace(cAtom.constraint());
			} else if (cAtom.type() == carl::FormulaType::VARCOMPARE) {
				// Note that we only add the polynomials here and don't really care about the relation
				// var ~ rootexpr(poly)
				// -> poly to ensure that the root exists
				//carl::Relation rel = cAtom.variable_comparison().negated() ? inverse(cAtom.variable_comparison().relation()) : cAtom.variable_comparison().relation();
				SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding bound " << cAtom << " -> " << carl::defining_polynomial(cAtom.variable_comparison()));
				cons.emplace(carl::defining_polynomial(cAtom.variable_comparison()), carl::Relation::NEQ);
				// removed (makes no sense):
				// -> var - poly to ensure that the relation still holds
				//cons.emplace(Poly(cAtom.variable_comparison().var()) - carl::defining_polynomial(cAtom.variable_comparison()), rel);
			} else if (cAtom.type() == carl::FormulaType::VARASSIGN) {
				SMTRAT_LOG_WARN("smtrat.nlsat", "Variable assignment " << cAtom << " should never get here!");
				assert(false);
				SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding assignment " << cAtom);
				const VariableComparisonT& vc = cAtom.variable_assignment();
				cons.emplace(carl::defining_polynomial(vc), carl::Relation::EQ);
			} else {
				SMTRAT_LOG_ERROR("smtrat.nlsat", "Unsupported formula type: " << cAtom);
				assert(false);
			}
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "-> " << cons);
		}
		return cons;
	}

} // namespace helper

class ExplanationGenerator {
private:
	using RAN = carl::RealAlgebraicNumber<Rational>;
	struct ProjectionSettings: public cad::BaseSettings {	
		static constexpr cad::Incrementality incrementality = cad::Incrementality::NONE;
		static constexpr cad::Backtracking backtracking = cad::Backtracking::ORDERED;
		static constexpr cad::ProjectionType projectionOperator = cad::ProjectionType::Hong;
	};

	Model mModel;
	// Store the original constraintAtoms, because they need to be added "raw" into the explanantion
	std::vector<FormulaT> mConstraints;
	cad::CADConstraints<ProjectionSettings::backtracking> mCADConstraints;
	cad::ModelBasedProjectionT<ProjectionSettings> mProjection;

	/**
	 * Construct expressions for the bounds of the CADCell component (a single sector/section)
	 * at the given level.
	 * @param boundsAsAtoms Output argument for cell component bounds at level as atomic formulas.
	 */
	void generateBoundsFor(FormulasT& boundsAsAtoms, carl::Variable var, std::size_t level, const Model& model) const {
		auto val = mModel.evaluated(var);
		assert(val.isRational() || val.isRAN());
		RAN value = val.isRational() ? RAN(val.asRational()) : val.asRAN();
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Generating bounds for " << var << " = " << value);
		std::optional<std::pair<RAN,FormulaT>> lower;
		std::optional<std::pair<RAN,FormulaT>> upper;

		for (std::size_t pid = 0; pid < mProjection.size(level); pid++) {
			const auto& poly = mProjection.getPolynomialById(level, pid);
			if (carl::is_zero(carl::substitute(poly, model))) continue;
			auto polyvars = carl::variables(poly);
			polyvars.erase(poly.main_var());
			auto list = carl::real_roots(poly, *carl::get_ran_assignment(polyvars, mModel));
			if (list.is_nullified()) continue;
			assert(list.is_univariate());
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Looking at " << poly << " with roots " << list.roots());
			// Find the closest roots/rootIdx around value.
			std::size_t rootID = 1;
			for (const auto& root: list.roots()) {
				auto param = std::make_pair(Poly(poly), rootID);
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
			boundsAsAtoms.push_back(lower->second);
		}
		if (upper && lower != upper) {
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Upper bound:" << upper->second);
			boundsAsAtoms.push_back(upper->second);
		}
	}
public:
	ExplanationGenerator(const std::vector<FormulaT>& constraints, const std::vector<carl::Variable>& vars, carl::Variable, const Model& model):
		mModel(model),
		mConstraints(constraints),
		mCADConstraints(
			[&](const auto& p, std::size_t cid, bool isBound){ mProjection.addPolynomial(cad::projection::normalize(p), cid, isBound); },
			[&](const auto& p, std::size_t cid, bool isBound){ mProjection.addEqConstraint(cad::projection::normalize(p), cid, isBound); },
			[&](const auto& p, std::size_t cid, bool isBound){ mProjection.removePolynomial(cad::projection::normalize(p), cid, isBound); }
		),
		mProjection(mCADConstraints, mModel)
	{
		SMTRAT_LOG_TRACE("smtrat.nlsat", "Reset to " << vars);
		mCADConstraints.reset(vars);
		mProjection.reset();
		std::set<ConstraintT> cons = helper::convertToConstraints(mConstraints);

		for (const auto& c: cons) {
			mCADConstraints.add(c);
		}
		
		SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Starting with projection \n" << mProjection);
		
		for (std::size_t level = 2; level < mCADConstraints.vars().size(); level++) {
			mProjection.projectNextLevel(level);
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "After projecting into level " << level << "\n" << mProjection);
		}

		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Projection is\n" << mProjection);
	}

	/**
	 * Construct explanation in non-clausal form (without the impliedAtom/implication).
	 * It consists of atomic formulas as
	 * expressions for cell component bounds and the constraintAtoms for which a CAD was
	 * constructed. Each cell component creates zero, one or two explanation atoms.
	 * The impliedAtom is not added to facilitate conversion into a clausal form
	 * afterwards.
	 * */
	void generateExplanation(const FormulaT& impliedAtom, std::vector<FormulasT>& explainAtomsinLvls) const {
		// Model with assignments for variables we already have constructed bounds for
		Model submodel; // Start empty
		explainAtomsinLvls.resize(mCADConstraints.vars().size());
		
		// Start from the bottom to generate bound constraints. 
		for (int level = static_cast<int>(mCADConstraints.vars().size()) - 1; level >= 0; level--) {
			std::size_t lvl = static_cast<std::size_t>(level);
			carl::Variable varAtLvl = mCADConstraints.vars()[lvl];
			if (mModel.find(varAtLvl) == mModel.end()) continue;
			generateBoundsFor(explainAtomsinLvls[lvl], varAtLvl, lvl+1, submodel);
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Cell bounds for " << varAtLvl << ": " << explainAtomsinLvls[lvl]);
			submodel.emplace(varAtLvl, mModel.evaluated(varAtLvl));
		}

		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Collecting constraints from " << mConstraints);
		for (const auto& constraintAtom: mConstraints) {
			SMTRAT_LOG_DEBUG("smtrat.nlsat", "Considering " << constraintAtom);
			if (constraintAtom == impliedAtom.negated()) {
				SMTRAT_LOG_DEBUG("smtrat.nlsat", "Skipping " << constraintAtom);
				continue;
			}
			explainAtomsinLvls.back().emplace_back(constraintAtom);
		}
		SMTRAT_LOG_DEBUG("smtrat.nlsat", "Final: " << explainAtomsinLvls.back() << " -> " << impliedAtom);
	}

	/**
	 * Compute explanation in clausal form.
	 */
	mcsat::Explanation getExplanation(const FormulaT& impliedAtom) const {
		std::vector<FormulasT> explainAtomsInLevels;
		generateExplanation(impliedAtom, explainAtomsInLevels);
		// Convert e1,..,en => I into clause -e1,...,-en, I
		FormulasT explainClauseLiterals;
		for (const auto& explainAtoms: explainAtomsInLevels) {
			for (const auto& explainAtom: explainAtoms) {
					explainClauseLiterals.emplace_back(explainAtom.negated());
			}
		}
		if (!impliedAtom.is_true()) explainClauseLiterals.emplace_back(impliedAtom);
		return FormulaT(carl::FormulaType::OR, std::move(explainClauseLiterals));
	}
};

}
}
}
