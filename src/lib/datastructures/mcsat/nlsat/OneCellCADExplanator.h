#pragma once

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
  std::reverse(point.begin(), point.end());
  return carl::RealAlgebraicPoint<smtrat::Rational>(std::move(point));
}

inline
FormulaT lessFormula(const carl::Variable var, carl::MultivariateRoot<Poly> mvRoot) {
  carl::VariableComparison<Poly> varCmp(var, mvRoot, carl::Relation::LESS);
  return FormulaT(varCmp);
}

inline
FormulaT greaterFormula(const carl::Variable var, carl::MultivariateRoot<Poly> mvRoot) {
  carl::VariableComparison<Poly> varCmp(var, mvRoot, carl::Relation::GREATER);
    return FormulaT(varCmp);
}

inline
FormulaT eqFormula(const carl::Variable var, carl::MultivariateRoot<Poly> mvRoot) {
  carl::VariableComparison<Poly> varCmp(var, mvRoot, carl::Relation::EQ);
  return FormulaT(varCmp);
}

inline
std::vector<carl::Variable> prefix(const std::vector<carl::Variable> vars, std::size_t prefixSize) {
  std::vector<carl::Variable> prefixVars(vars.begin(), std::next(vars.begin(), prefixSize));
  return prefixVars;
}

inline
std::vector<onecellcad::TagPoly> toTagPoly (std::vector<Poly> polys) {
  std::vector<onecellcad::TagPoly> tPolys;
  for (auto& poly : polys)
    tPolys.emplace_back(onecellcad::TagPoly{onecellcad::PolyTag::SGN_INV, poly});

  return tPolys;
}

struct Explanation {
  boost::optional<FormulaT>
  operator()(const mcsat::Bookkeeping &assignState,
             const std::vector<carl::Variable> &varOrder,
             carl::Variable var,
             const FormulasT &reasonAtoms,
             const FormulaT &impliedAtom) const
  {
    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "With: " << reasonAtoms << " explain: " << impliedAtom);
    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat","Ascending variable order: " << varOrder
      << " and eliminate down from: " << var);

    std::vector<Poly> polys;
//  	if (!impliedAtom.isFalse() && !impliedAtom.isTrue())
//  	  polys.emplace_back(extractPoly(impliedAtom));

    for (const auto &constraint : helper::convertToConstraints(reasonAtoms))
      polys.emplace_back(constraint.lhs()); // constraints have the form e.g. 'poly < 0'

    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", assignState);
    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Number of assigned vars: " << assignState.model().size());
    auto maxNormalLvl = assignState.model().size()-1; // -1, b/c we count first var = poly level 0
    std::vector<std::vector<onecellcad::TagPoly>> projectionLevels(varOrder.size()); // init all levels with empty vector
    carl::CoCoAAdaptor<Poly>factorizer(polys);
    onecellcad::categorizeByLevel(projectionLevels,
                                  varOrder,
                                  onecellcad::nonConstIrreducibleFactors(factorizer, toTagPoly(polys)));

    // Project higher level polys down to "normal" level
    auto maxLevel = varOrder.size() - 1;
    for (std::size_t currentLvl = maxLevel; currentLvl > maxNormalLvl; currentLvl--) {
      onecellcad::categorizeByLevel(
        projectionLevels,
        varOrder,
        onecellcad::nonConstIrreducibleFactors(
          factorizer, onecellcad::singleLevelFullProjection(varOrder[currentLvl], projectionLevels[currentLvl])));
    }

    std::vector<onecellcad::TagPoly2> normalLevelPolys;
    for (int currentLvl = maxNormalLvl; currentLvl >= 0; currentLvl--) {
      for (auto& poly : projectionLevels[currentLvl])
        normalLevelPolys.emplace_back(onecellcad::TagPoly2{poly.tag, poly.poly, static_cast<size_t>(currentLvl)});
    }
    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "All projected level polys: " << normalLevelPolys);

    auto cellOpt = onecellcad::OneCellCAD().pointEnclosingCADCell(
      prefix(varOrder, maxNormalLvl+1), asRANPoint(assignState), normalLevelPolys);
    if (!cellOpt) {
      SMTRAT_LOG_WARN("smtrat.mcsat.nlsat", "OneCell construction failed");
      return boost::none;
    }

    auto cell = *cellOpt;
    // We directly construct the clausal-formula of 'E -> F',
    // where E is the conjunction of reasonAtom and CAD cell bound constraints, and F is the implication.
    FormulasT explainLiterals; // -e1 v -e2 v ..., where - is not

    for (const auto& reasonAtom : reasonAtoms)
      explainLiterals.emplace_back(reasonAtom.negated());

    for (std::size_t i = 0; i < cell.size(); i++) {
      auto& cellComponent = cell[i];
      auto cellVariable = varOrder[i];
      if (mpark::holds_alternative<onecellcad::Section>(cellComponent)) {
        auto sectionPoly = mpark::get<onecellcad::Section>(cellComponent).poly;
        auto rootNumber = mpark::get<onecellcad::Section>(cellComponent).rootNumber;
        // Need to use poly with its main variable replaced by the special MultivariateRootT::var().
        auto param = std::make_pair(Poly(carl::UnivariatePolynomial<Poly>(MultivariateRootT::var(), sectionPoly.toUnivariatePolynomial(cellVariable).coefficients())), rootNumber);
        explainLiterals.emplace_back(helper::buildAbove(cellVariable, param).negated());
      } else {
        auto sectorLowPoly = mpark::get<onecellcad::Sector>(cellComponent).lowBound;
        auto sectorHighPoly = mpark::get<onecellcad::Sector>(cellComponent).highBound;
        if (sectorLowPoly) {
          // Need to use poly with its main variable replaced by the special MultivariateRootT::var().
          auto param = std::make_pair(Poly(carl::UnivariatePolynomial<Poly>(MultivariateRootT::var(),
                                                                            sectorLowPoly->poly.toUnivariatePolynomial(
                                                                              cellVariable).coefficients())),
                                      sectorLowPoly->rootNumber);
          explainLiterals.emplace_back(helper::buildAbove(cellVariable, param).negated());
        }
        if (sectorHighPoly) {
          // Need to use poly with its main variable replaced by the special MultivariateRootT::var().
          auto param = std::make_pair(Poly(carl::UnivariatePolynomial<Poly>(MultivariateRootT::var(),
                                                                            sectorHighPoly->poly.toUnivariatePolynomial(
                                                                              cellVariable).coefficients())),
                                      sectorHighPoly->rootNumber);
          explainLiterals.emplace_back(helper::buildAbove(cellVariable, param).negated());
        }
      }
    }

    if (!impliedAtom.isTrue() && !impliedAtom.isFalse())
      explainLiterals.emplace_back(impliedAtom);

    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Explain literals: " << explainLiterals);
    return FormulaT(carl::FormulaType::OR, explainLiterals); // need to return a clause (L1 v L2 v ...)
  }
};
} // namespace nlsat
} // namespace mcsat
} // namespace smtrat


