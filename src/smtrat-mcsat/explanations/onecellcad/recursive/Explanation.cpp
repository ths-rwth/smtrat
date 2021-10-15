#include "Explanation.h"
#include "OneCellCAD.h"

#include <smtrat-mcsat/explanations/nlsat/ExplanationGenerator.h>

#include "new/first_level.h"

namespace smtrat {
namespace mcsat {
namespace onecellcad {
namespace recursive {


inline void setNullification(bool n){
	cover_nullification = n;
}

template<class Setting1, class Setting2>
boost::optional<mcsat::Explanation> Explanation<Setting1,Setting2>::operator()(const mcsat::Bookkeeping& trail, // current assignment state
						carl::Variable var,
						const FormulasT& trailLiterals, bool) const {
	
	bool covering_at_first_level=false;
	bool strict_unassigned_handling=false;

	assert(trail.model().size() == trail.assignedVariables().size());

#ifdef SMTRAT_DEVOPTION_Statistics
	getStatistic().explanationCalled();
#endif

	#if not (defined USE_COCOA || defined USE_GINAC)
		// OneCellCAD needs carl::irreducibleFactors to be implemented
		#warning OneCellCAD may be incorrect as USE_COCOA is disabled
	#endif

    // compute compatible complete variable ordering
    std::vector varOrder(trail.assignedVariables());
    varOrder.push_back(var);
    for (const auto& v : trail.variables()) {
        if (std::find(varOrder.begin(), varOrder.end(), v) == varOrder.end()) {
            varOrder.push_back(v);
        }
    }

    // Temp. workaround, should at least one theory-var should be assigned, otherwise no OneCell construct possible
    // TODO remove as soon, mcsat backend handles this case.
    if (trail.assignedVariables().size() == 0) {
        SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", " OneCellExplanation called with 0 theory-assignment");
        FormulasT explainLiterals;
        for (const auto& trailLiteral : trailLiterals)
            explainLiterals.emplace_back(trailLiteral.negated());
        return boost::variant<FormulaT, ClauseChain>(FormulaT(carl::FormulaType::OR, std::move(explainLiterals)));
    }
    assert(trail.assignedVariables().size() > 0);

    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Starting an explanation");
    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", trail);
    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Number of assigned vars: " << trail.model().size());
    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Trail literals: " << trailLiterals); //<< " Implied literal: " << impliedLiteral);
    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Ascending variable order: " << varOrder
                                                                        << " and eliminate down from: " << var);

    const auto& trailVariables = trail.assignedVariables();
    std::vector<carl::Variable> fullProjectionVarOrder = varOrder;
    std::vector<carl::Variable> oneCellCADVarOrder;
    for (std::size_t i = 0; i < trailVariables.size(); i++)
        oneCellCADVarOrder.emplace_back(fullProjectionVarOrder[i]);

    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Ascending OneCellVarOrder: " << oneCellCADVarOrder);

    std::size_t oneCellMaxLvl = trail.model().size() - 1;											  // -1, b/c we count first var = poly level 0
    std::vector<std::vector<TagPoly>> projectionLevels(fullProjectionVarOrder.size()); // init all levels with empty vector

    std::vector<Poly> polys; // extract from trailLiterals
    for (const auto& constraint : nlsat::helper::convertToConstraints(trailLiterals))
        polys.emplace_back(constraint.lhs()); // constraints have the form 'poly < 0' with  <, = etc.

    //Fill projectionLevels
    for(const auto& poly : polys){
        appendOnCorrectLevel(poly, InvarianceType::SIGN_INV, projectionLevels, varOrder);
    }

    // Project higher level polys down to "normal" level
    carl::RealAlgebraicPoint<Rational> point = asRANPoint(trail).prefixPoint(oneCellMaxLvl + 1);
    auto maxLevel = fullProjectionVarOrder.size() - 1;
    while (projectionLevels[maxLevel].empty() && maxLevel > 0) {
        projectionLevels.erase(projectionLevels.begin() + maxLevel);
        maxLevel--;
    }
    assert(maxLevel > 0 || !projectionLevels[0].empty());

    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Polys at levels before full CAD projection:\n"
            << projectionLevels);

    RecursiveCAD cad = RecursiveCAD(fullProjectionVarOrder, point);
    for (std::size_t currentLvl = maxLevel; currentLvl > oneCellMaxLvl; currentLvl--) {
        auto currentVar = fullProjectionVarOrder[currentLvl];
        assert(currentLvl >= 1);

        if(currentLvl == oneCellMaxLvl+1){
            bool failcheck = optimized_singleLevelFullProjection(currentVar, currentLvl, projectionLevels, cad);
            if(!failcheck){
                SMTRAT_LOG_WARN("smtrat.mcsat.nlsat", "OneCell construction failed");
                return boost::none;
            }
        } else{
            singleLevelFullProjection(fullProjectionVarOrder, currentVar, currentLvl, projectionLevels);
        }

        projectionLevels.erase(projectionLevels.begin() + currentLvl);
        SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Polys at levels after a CAD projection at level: " << currentLvl << ":\n" << projectionLevels);
    }

    if(Setting2::heuristic == 1){
        // reorder polynomials in ascending order by degree
        for (int i = (int)projectionLevels.size()-1; i >= 0; i--){
            for(auto & tpoly : projectionLevels[i]){
                tpoly.deg = getDegree(tpoly, fullProjectionVarOrder[i]);
                SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Add level of poly: " << tpoly.deg);
            }
            std::sort(projectionLevels[i].begin(), projectionLevels[i].end(), [](auto const &t1, auto const &t2) {
                return t1.deg < t2.deg;
            });
        }
    } else if(Setting2::heuristic == 2){
        // reorder polynomials in descending order by degree
        for (int i = (int)projectionLevels.size()-1; i >= 0; i--){
            for(auto & tpoly : projectionLevels[i]){
                tpoly.deg = getDegree(tpoly, fullProjectionVarOrder[i]);
                SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Add level of poly: " << tpoly.deg);
            }
            std::sort(projectionLevels[i].begin(), projectionLevels[i].end(), [](auto const &t1, auto const &t2) {
                return t1.deg > t2.deg;
            });
        }
    } else if(Setting2::heuristic != 0){
        SMTRAT_LOG_WARN("smtrat.mcsat.nlsat", "Invalid heuristic input");
    }
    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Polys after possible reordering: \n" << projectionLevels);

	setNullification(Setting1::cover_nullification);
	std::optional<CADCell> cellOpt = cad.pointEnclosingCADCell(projectionLevels);
	if (!cellOpt) {
		SMTRAT_LOG_WARN("smtrat.mcsat.nlsat", "OneCell construction failed");
		return boost::none;
	}

	auto cell = *cellOpt;
	SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Constructed cell: " << cell);

	// If we have trail literals: L_M, ... , L_M,
	// an implied literal L
	// and cell boundary atoms : A, .., A
	// We construct the formula '(A & ... & A & L_M & ... & L_M) => L'
	// in its clausal form 'E := (-A v ... v -A v -L_M v ... v -L_M  v L)'
	// as our explanation.
	FormulasT explainLiterals;

	for (const auto& trailLiteral : trailLiterals)
		explainLiterals.emplace_back(trailLiteral.negated());

	for (std::size_t i = 0; i < cell.size(); i++) {
		auto& cellComponent = cell[i];
		auto cellVariable = oneCellCADVarOrder[i];
		if (std::holds_alternative<Section>(cellComponent)) {
			auto section = std::get<Section>(cellComponent).boundFunction;
			// Need to use poly with its main variable replaced by the special MultivariateRootT::var().
			auto param = std::make_pair(section.poly(), section.k());
			explainLiterals.emplace_back(nlsat::helper::buildEquality(cellVariable, param).negated());
		} else {
			auto sectorLowBound = std::get<Sector>(cellComponent).lowBound;
			if (sectorLowBound) {
				// Need to use poly with its main variable replaced by the special MultivariateRootT::var().
				auto param = std::make_pair(sectorLowBound->boundFunction.poly(), sectorLowBound->boundFunction.k());
				explainLiterals.emplace_back(nlsat::helper::buildAbove(cellVariable, param).negated());
			}
			auto sectorHighBound = std::get<Sector>(cellComponent).highBound;
			if (sectorHighBound) {
				// Need to use poly with its main variable replaced by the special MultivariateRootT::var().
				auto param = std::make_pair(sectorHighBound->boundFunction.poly(), sectorHighBound->boundFunction.k());
				explainLiterals.emplace_back(nlsat::helper::buildBelow(cellVariable, param).negated());
			}
		}
	}

	//    if (!impliedLiteral.isFalse())
	//      explainLiterals.emplace_back(impliedLiteral);

	SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Explain literals: " << explainLiterals);
#ifdef SMTRAT_DEVOPTION_Statistics
	getStatistic().explanationSuccess();
#endif
	return boost::variant<FormulaT, ClauseChain>(FormulaT(carl::FormulaType::OR, std::move(explainLiterals)));
}

// Instantiations
template struct Explanation<CoverNullification, NoHeuristic>;
template struct Explanation<DontCoverNullification, NoHeuristic>;
template struct Explanation<DontCoverNullification, DegreeAscending>;
template struct Explanation<DontCoverNullification, DegreeDescending>;

} // namespace recursive
} // namespace onecellcad
} // namespace mcsat
} // namespace smtrat
