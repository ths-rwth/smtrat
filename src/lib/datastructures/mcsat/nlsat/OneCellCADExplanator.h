#pragma once

#include <algorithm>

#include "../../../Common.h"
#include "../Bookkeeping.h"
#include "../onecellcad/OneCellCAD.h"
#include "ExplanationGenerator.h"

namespace smtrat {
namespace mcsat {
namespace nlsat {

inline
carl::RealAlgebraicPoint<smtrat::Rational> asRANPoint(
  const mcsat::Bookkeeping &data) {
  std::vector<carl::RealAlgebraicNumber<smtrat::Rational>> point;
  for (const auto variable : data.assignedVariables()) {
    const auto& modelValue = data.model().evaluated(variable);
    assert(modelValue.isRational() || modelValue.isRAN());
    modelValue.isRational() ?
      point.emplace_back(modelValue.asRational()) : point.emplace_back(modelValue.asRAN());
  }
  return carl::RealAlgebraicPoint<smtrat::Rational>(std::move(point));
}

template <typename T>
std::vector<T> prefix(const std::vector<T> vars, std::size_t prefixSize) {
  std::vector<T> prefixVars(vars.begin(), std::next(vars.begin(), (long) prefixSize));
  return prefixVars;
}

inline
std::vector<onecellcad::TagPoly> toTagPoly (std::vector<Poly> polys) {
  std::vector<onecellcad::TagPoly> tPolys;
  for (auto& poly : polys)
    tPolys.emplace_back(onecellcad::TagPoly{onecellcad::InvarianceType::SIGN_INV, poly});

  return tPolys;
}

inline
ostream& operator<<(ostream& os, const std::vector<std::vector<onecellcad::TagPoly>>& lvls)
{
  int lvl = (int) lvls.size() - 1;
  for (auto it = lvls.rbegin(); it != lvls.rend(); ++it) {
    os << lvl << ": ";
    os << *it << "\n";
    lvl--;
  }
  return os;
}

  struct OneCellExplanation {
  boost::optional<mcsat::Explanation>
  operator()(const mcsat::Bookkeeping &trail, // current assignment state
             const std::vector<carl::Variable> &varOrder,
             carl::Variable var,
             const FormulasT &trailLiterals) const
  {
    assert(trail.model().size() == trail.assignedVariables().size());

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
    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Trail literals: " << trailLiterals ); //<< " Implied literal: " << impliedLiteral);
    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat","Ascending variable order: " << varOrder
      << " and eliminate down from: " << var);

    std::vector<Poly> polys; // extract from trailLiterals
    for (const auto &constraint : helper::convertToConstraints(trailLiterals))
      polys.emplace_back(constraint.lhs()); // constraints have the form 'poly < 0' with  <, = etc.

    const auto& trailVariables = trail.assignedVariables();
    std::vector<carl::Variable> fullProjectionVarOrder(trailVariables.size());
    std::vector<carl::Variable> oneCellCADVarOrder;
    fullProjectionVarOrder.reserve(varOrder.size());
    oneCellCADVarOrder.reserve(trailVariables.size());

    for (auto variable : varOrder) {
      if (std::find(trailVariables.begin(), trailVariables.end(), variable) == trailVariables.end())
        fullProjectionVarOrder.push_back(variable);
      else
        oneCellCADVarOrder.push_back(variable);
    }
    std::copy_n(oneCellCADVarOrder.begin(), oneCellCADVarOrder.size(), fullProjectionVarOrder.begin());

    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "FullProjVarOrder: " << fullProjectionVarOrder);
    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "OneCellVarOrder: " << oneCellCADVarOrder);
    std::size_t oneCellMaxLvl = trail.model().size()-1; // -1, b/c we count first var = poly level 0
    std::vector<std::vector<onecellcad::TagPoly>> projectionLevels(fullProjectionVarOrder.size()); // init all levels with empty vector
    carl::CoCoAAdaptor<Poly>factorizer(polys);
    onecellcad::categorizeByLevel(
      projectionLevels,
      fullProjectionVarOrder,
      onecellcad::nonConstIrreducibleFactors(factorizer, toTagPoly(polys)));

    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Polys at levels before full CAD projection:\n" << projectionLevels);
    // Project higher level polys down to "normal" level
    auto maxLevel = fullProjectionVarOrder.size() - 1;
    for (std::size_t currentLvl = maxLevel; currentLvl > oneCellMaxLvl; currentLvl--) {
      auto currentVar = fullProjectionVarOrder[currentLvl];
      auto projectionFactors = onecellcad::singleLevelFullProjection(currentVar, projectionLevels[currentLvl]);
      onecellcad::categorizeByLevel(
        projectionLevels,
        fullProjectionVarOrder,
        onecellcad::nonConstIrreducibleFactors(
          factorizer, projectionFactors));
      projectionLevels[currentLvl].clear();
      SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Polys at levels after projecting level " << currentLvl << ":\n" << projectionLevels);
    }

    std::vector<onecellcad::TagPoly2> oneCellPolys;
    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "OneCellMaxLvl: " << oneCellMaxLvl << " ProjectionLvls: " << projectionLevels);
    for (std::size_t currentLvl = 0; currentLvl <= oneCellMaxLvl; currentLvl++) {
      for (const auto& poly : projectionLevels[currentLvl])
        oneCellPolys.emplace_back(onecellcad::TagPoly2{poly.tag, poly.poly, currentLvl});
    }
    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "All polys for OneCell construction: " << oneCellPolys);

    auto cellOpt = onecellcad::OneCellCAD(oneCellCADVarOrder,asRANPoint(trail).prefixPoint(oneCellMaxLvl+1)).pointEnclosingCADCell(
      oneCellPolys);
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
      if (mpark::holds_alternative<onecellcad::Section>(cellComponent)) {
        auto section = mpark::get<onecellcad::Section>(cellComponent).boundFunction;
        // Need to use poly with its main variable replaced by the special MultivariateRootT::var().
        auto param = std::make_pair(section.poly(), section.rootIdx());
        explainLiterals.emplace_back(helper::buildEquality(cellVariable, param).negated());
      } else {
        auto sectorLowBound = mpark::get<onecellcad::Sector>(cellComponent).lowBound;
        if (sectorLowBound) {
          // Need to use poly with its main variable replaced by the special MultivariateRootT::var().
          auto param = std::make_pair(sectorLowBound->boundFunction.poly(), sectorLowBound->boundFunction.rootIdx());
          explainLiterals.emplace_back(helper::buildAbove(cellVariable, param).negated());
        }
        auto sectorHighBound = mpark::get<onecellcad::Sector>(cellComponent).highBound;
        if (sectorHighBound) {
          // Need to use poly with its main variable replaced by the special MultivariateRootT::var().
          auto param = std::make_pair(sectorHighBound->boundFunction.poly(), sectorHighBound->boundFunction.rootIdx());
          explainLiterals.emplace_back(helper::buildBelow(cellVariable, param).negated());
        }
      }
    }

//    if (!impliedLiteral.isFalse())
//      explainLiterals.emplace_back(impliedLiteral);

    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Explain literals: " << explainLiterals);
    return boost::variant<FormulaT, ClauseChain>(FormulaT(carl::FormulaType::OR, std::move(explainLiterals)));
  }
};
} // namespace nlsat
} // namespace mcsat
} // namespace smtrat


