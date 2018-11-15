#pragma once

#include "CAD.h"
#include "../../cad/Settings.h"
#include "../../cad/helper/CADCore.h"
#include "../../cad/projection/Projection.h"
#include "../../cad/lifting/LiftingTree.h"
#include "../../cad/lifting/Sample.h"

#include <carl/formula/model/Model.h>
#include <carl/formula/model/ran/RealAlgebraicNumberEvaluation.h>
#include <carl/core/Sign.h>
#include <carl/core/MultivariatePolynomial.h>
#include <carl/core/UnivariatePolynomial.h>
#include <carl/core/polynomialfunctions/Factorization.h>
#include <carl/core/Relation.h>

#include <iostream>
#include <map>
#include <vector>
#include <string>
#include <algorithm>
#include <utility>

namespace smtrat::qe::cad {

  struct CADSettings : smtrat::cad::BaseSettings {
    static constexpr smtrat::cad::ProjectionType projectionOperator = smtrat::cad::ProjectionType::Brown;
    static constexpr smtrat::cad::Incrementality incrementality = smtrat::cad::Incrementality::NONE;
    static constexpr smtrat::cad::Backtracking backtracking = smtrat::cad::Backtracking::UNORDERED;
  };

  class QE {
  private:
    FormulaT mQuantifierFreePart;
    std::vector<carl::Variable> mVariables;
    std::vector<ConstraintT> mConstraints;
    std::vector<std::pair<QuantifierType,carl::Variable>> mQuantifiers;

    std::size_t n;
    std::size_t k;

    CAD<CADSettings> mCAD;

	using TreeIT = CAD<CADSettings>::TreeIterator;

    std::map<TreeIT, bool> mTruth;
    std::map<TreeIT, std::vector<carl::Sign>> mSignature;

    std::vector<std::pair<TreeIT,TreeIT>> mCauseConflict;

    std::vector<TreeIT> mTrueSamples;
    std::vector<TreeIT> mFalseSamples;
    FormulasT mAtomicFormulas;

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
    QE(const FormulaT &quantifierFreePart, const QEQuery& quantifiers);
    FormulaT eliminateQuantifiers();
  };

}
