#pragma once

#include "../../../Common.h"
#include "../Bookkeeping.h"
//#include "../../cad/projection/Projection.h"
//#include "../common.h"
#include "../onecellcad/OneCellCAD.h"

/*#include <carl/util/Common.h>
#include <carl/formula/model/ModelVariable.h>
#include <carl/formula/model/ModelValue.h>
#include <carl/core/MultivariatePolynomial.h>*/

namespace smtrat {
namespace mcsat {
namespace nlsat {
inline
void add(std::vector<Poly> &polys, const FormulaT &formula) {
	if (formula.getType() == carl::FormulaType::CONSTRAINT) {
    SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding " << formula);
    polys.emplace_back(formula.constraint().lhs());
  } else if (formula.getType() == carl::FormulaType::VARCOMPARE) {
    SMTRAT_LOG_DEBUG("smtrat.nlsat", "Adding bound " << formula);
    polys.emplace_back(formula.variableComparison().definingPolynomial());
  } else if (formula.getType() == carl::FormulaType::VARASSIGN) {
    SMTRAT_LOG_WARN("smtrat.nlsat", "Variable assignment " << formula << " should never get here!");
    assert(false);
  } else {
    SMTRAT_LOG_ERROR("smtrat.nlsat", "Unsupported formula type: " << formula);
    assert(false);
  }
}

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

struct Explanation {
  boost::optional<FormulaT>
  operator()(const mcsat::Bookkeeping &data, const std::vector<carl::Variable> &variableOrder, carl::Variable var,
             const FormulasT &reason, const FormulaT &implication) const {
    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "With: " << reason << " explain: " << implication);
    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat",
                     "Ascending variable order: " << variableOrder << " and eliminate down from: " << var);

    std::vector<Poly> polys;
  	if (!implication.isFalse() && !implication.isTrue())
      add(polys, implication);

    for (const auto &formula : reason)
      add(polys, formula);

    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Bookkeep: " << data);
    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Normal max poly level: " << data.model().size() - 1);
    auto maxNormalPolyLevel = data.model().size()-1;
    auto maxHigherPolyLevel = variableOrder.size()-1;
    std::vector<std::vector<onecellcad::TagPoly>> higherLevelPolys(variableOrder.size()-1 - maxNormalPolyLevel);
    std::vector<onecellcad::TagPoly2> normalLevelPolys;
    for (const auto& poly : polys) {
      auto polyLevel = *onecellcad::levelOf(variableOrder, poly);
      if (polyLevel > maxNormalPolyLevel)
        higherLevelPolys[polyLevel-maxNormalPolyLevel-1].push_back(
          {onecellcad::PolyTag::SGN_INV, poly});
      else
        normalLevelPolys.push_back(
          {onecellcad::PolyTag::SGN_INV, poly, polyLevel});
    }
    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Normal level Polys: " << normalLevelPolys);
//    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Higher level Polys: " << onecellcad::asMultiPolys(higherLevelPolys));
    // Project higher level polys down to "normal" level
    carl::CoCoAAdaptor<Poly>factorizer(polys);
    for (std::size_t levelToProject = maxHigherPolyLevel; levelToProject > maxNormalPolyLevel; levelToProject--) {
      for (auto& poly : onecellcad::OneCellCAD().oneLevelFullBrowMcCallumProjection(
            factorizer, variableOrder[levelToProject], higherLevelPolys[levelToProject-maxNormalPolyLevel-1])) {
        auto polyLevel = *onecellcad::levelOf(variableOrder, poly.poly);
        if (polyLevel > maxNormalPolyLevel) // put projected polys into correct level bin.
          higherLevelPolys[polyLevel-maxNormalPolyLevel-1].push_back(poly);
        else
          normalLevelPolys.push_back({poly.tag, poly.poly, polyLevel});
      }
    }
    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "All projected level polys: " << normalLevelPolys);

    auto cellOpt = onecellcad::OneCellCAD().pointEnclosingCADCell(
      prefix(variableOrder, data.model().size()), asRANPoint(data), normalLevelPolys);
    if (!cellOpt)
      assert (false); // TODO call other explanator if onecellcad fails

    auto cell = *cellOpt;
    // We construct the clausal-formula of 'E -> F',
    // where E is the conjunction of CAD cell constraints and F is the implication.
    FormulasT explainLiterals;
    if (!implication.isTrue() && !implication.isFalse())
      explainLiterals.emplace_back(implication);

    for (std::size_t i = 0; i < cell.size(); i++) {
      auto& cellComponent = cell[i];
      auto cellVariable = variableOrder[i];
      if (mpark::holds_alternative<onecellcad::Section>(cellComponent)) {
        auto sectionPoly = mpark::get<onecellcad::Section>(cellComponent).poly;
        auto rootNumber = mpark::get<onecellcad::Section>(cellComponent).rootNumber;
        explainLiterals.emplace_back(
          eqFormula(cellVariable, MultivariateRootT(sectionPoly, rootNumber)).negated());
      } else {
        auto sectorLowPoly = mpark::get<onecellcad::Sector>(cellComponent).lowBound;
        auto sectorHighPoly = mpark::get<onecellcad::Sector>(cellComponent).highBound;
        if (sectorLowPoly)
          explainLiterals.emplace_back(
            greaterFormula(cellVariable, MultivariateRootT(sectorLowPoly->poly, sectorLowPoly->rootNumber)).negated());
        if (sectorHighPoly)
          explainLiterals.emplace_back(
            lessFormula(cellVariable, MultivariateRootT(sectorHighPoly->poly, sectorHighPoly->rootNumber)).negated());
      }
    }
    SMTRAT_LOG_DEBUG("smtrat.mcsat.nlsat", "Explain literals: " << explainLiterals);
    return FormulaT(carl::FormulaType::OR, explainLiterals); // need to return a clause (L1 v L2 v ...)
  }
};
} // namespace nlsat
} // namespace mcsat
} // namespace smtrat


