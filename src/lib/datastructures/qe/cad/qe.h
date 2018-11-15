#pragma once

#include "Common.h"

#include "CAD_QE.h"
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

namespace smtrat{
namespace qe{
  struct CADSettings : smtrat::cad::BaseSettings {
    static constexpr smtrat::cad::ProjectionType projectionOperator = smtrat::cad::ProjectionType::Brown;
    static constexpr smtrat::cad::Incrementality incrementality = smtrat::cad::Incrementality::NONE;
    static constexpr smtrat::cad::Backtracking backtracking = smtrat::cad::Backtracking::UNORDERED;
  };

  class QE {
  private:
    Formula mQuantifierFreePart;
    Variables mVariables;
    Constraints mConstraints;
    std::vector<std::pair<QuantifierType,Variable>> mQuantifiers;

    std::size_t n;
    std::size_t k;

    smtrat::cad::CAD_QE<CADSettings> mCAD;

    std::map<carl::tree<smtrat::cad::Sample>::iterator, bool> mTruth;
    std::map<carl::tree<smtrat::cad::Sample>::iterator, std::vector<carl::Sign>> mSignature;

    std::vector<std::pair<carl::tree<smtrat::cad::Sample>::iterator,carl::tree<smtrat::cad::Sample>::iterator>> mCauseConflict;

    std::vector<carl::tree<smtrat::cad::Sample>::iterator> mTrueSamples;
    std::vector<carl::tree<smtrat::cad::Sample>::iterator> mFalseSamples;
    Formulas mAtomicFormulas;

    void constructCAD();
    void updateCAD(Polynomials& polynomials);

    void simplifyCAD();
    bool truthBoundaryTest(carl::tree<smtrat::cad::Sample>::iterator& b, carl::tree<smtrat::cad::Sample>::iterator& c, carl::tree<smtrat::cad::Sample>::iterator& d);

    void computeTruthValues();
    void computeSignatures();

    bool isProjectionDefinable();
    void makeProjectionDefinable();

    Formula constructImplicant(const carl::tree<smtrat::cad::Sample>::iterator& sample);
    Formula constructSolutionFormula();

    template<typename T>
    std::vector<T> computeHittingSet(const std::vector<std::vector<T>>& setOfSets);
  public:
    QE(const Formula &quantifierFreePart, const QEQuery& quantifiers);
    Formula eliminateQuantifiers();
  };

}
}
