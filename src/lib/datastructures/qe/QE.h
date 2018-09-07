#pragma once

#include "Common.h"

#include "../../../cli/parser/theories/TheoryTypes.h"

#include "CAD_QE/CAD_QE.h"
#include "../cad/Settings.h"
#include "../cad/helper/CADCore.h"
#include "../cad/projection/Projection.h"
#include "../cad/lifting/LiftingTree.h"
#include "../cad/lifting/Sample.h"

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
#include <algorithm> // fuer std::transform, std::find
#include <utility> // fuer std::pair

namespace smtrat{
namespace qe{
  /* CADSettings beeinhaltet die Einstellung fuer die CAD
  * - Wir konfigurieren uns die Settings fuer die Quantifier Elimination
  * - CADSettings erbt im wesentlichen alle Einstellungen der BaseSettings
  * - Lediglich die Einstellung CoreHeuristic wird angepasst: Wir setzen diese auf EnumerateAll
  * - EnumerateAll fuehrt dazu, dass ein vollstaendiger LifingTree aufgebaut wird
  */
  struct CADSettings : smtrat::cad::BaseSettings {
    // Verwende Brown's Projektionsoperator
    static constexpr smtrat::cad::ProjectionType projectionOperator = smtrat::cad::ProjectionType::Brown;

    static constexpr smtrat::cad::Backtracking backtracking = smtrat::cad::Backtracking::UNORDERED;

    // Die Originale Metode, beschrieben in Col75, benutzt Collins Projektionsoperator
    // static constexpr smtrat::cad::ProjectionType projectionOperator = smtrat::cad::ProjectionType::Collins;
  };

  /* QE Klasse
  * -
  */
  class QE {
  private:
    // Daten //////////////////////////////////////////////////////////////
    Formula mQuantifierFreePart;
    Variables mVariables;
    Constraints mConstraints;
    std::map<Variable, smtrat::parser::QuantifierType> mQuantifiers;

    std::size_t n;
    std::size_t k;

    smtrat::cad::CAD_QE<CADSettings> mCAD;

    std::map<carl::tree<smtrat::cad::Sample>::iterator, bool> mTruth;
    std::map<carl::tree<smtrat::cad::Sample>::iterator, std::vector<carl::Sign>> mSignature;

    std::vector<std::pair<carl::tree<smtrat::cad::Sample>::iterator,carl::tree<smtrat::cad::Sample>::iterator>> mCauseConflict;

    std::vector<carl::tree<smtrat::cad::Sample>::iterator> mTrueSamples;
    std::vector<carl::tree<smtrat::cad::Sample>::iterator> mFalseSamples;
    Formulas mAtomicFormulas;

    // Private-Funktionen /////////////////////////////////////////////////
    void constructCAD();
    void updateCAD(Constraints& constraints);
    void simplifyCAD();

    bool truthBoundaryTest(carl::tree<smtrat::cad::Sample>::iterator& b, carl::tree<smtrat::cad::Sample>::iterator& c, carl::tree<smtrat::cad::Sample>::iterator& d);

    void computeTruthValues();
    void computeSignatures();

    bool isProjectionDefinable();
    void makeProjectionDefinable();

    Formula constructImplicant(const carl::tree<smtrat::cad::Sample>::iterator& sample);
    Formula constructSolutionFormula();

    // Originale Methode zur Konstruktion von solution formulas, beschrieben in Col75
    Formula constructSolutionFormula_OriginalMethod();

    template<typename T>
    std::vector<T> computeHittingSet(const std::vector<std::vector<T>>& setOfSets);

    void printCADCellsPerLevel(std::size_t level);
    void printProjectionFactorsPerLevel(std::size_t level);
  public:
    // Public-Funktionen //////////////////////////////////////////////////
    QE(Formula &quantifierFreePart, std::map<Variable, smtrat::parser::QuantifierType>& quantifiers);
    Formula eliminateQuantifiers();
  };
} // End of namespace qe
} // End of namespace smtrat
