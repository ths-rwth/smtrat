#include "qe.h"

#include <sstream>

namespace smtrat{
namespace qe{

  QE::QE(const Formula& quantifierFreePart, const QEQuery& quantifiers) {
    mQuantifierFreePart = quantifierFreePart;
	mQuantifiers = smtrat::flattenQEQuery(quantifiers);

	carl::carlVariables vars;
	quantifierFreePart.gatherVariables(vars);
    // quantified variables
	for (const auto& v: mQuantifiers) {
		mVariables.emplace_back(v);
		vars.erase(v);
	}
	for (auto v: vars.underlyingVariables()) {
		mVariables.emplace_back(v);
	}
    
    // number of variables
    n = mVariables.size();
    // number of free variables
    k = mVariables.size() - mQuantifiers.size();

    mQuantifierFreePart.getConstraints(mConstraints);
  }

  Formula QE::eliminateQuantifiers() {
    constructCAD();

    computeTruthValues();

    simplifyCAD();

    if(!isProjectionDefinable()) {
      SMTRAT_LOG_DEBUG("smtrat.qe", "The CAD is not projection-definable");
      makeProjectionDefinable();
    }else{
      SMTRAT_LOG_DEBUG("smtrat.qe", "The CAD is already projection-definable");
    }

    return constructSolutionFormula();
  }

  void QE::constructCAD() {
    mCAD.reset(mVariables);

    for(Constraints::iterator it = mConstraints.begin(); it != mConstraints.end(); it++) {
      mCAD.addPolynomial(it->lhs());
    }

    mCAD.project();
    mCAD.lift();
  }

  void QE::updateCAD(Polynomials& polynomials) {
    // polynomials with lowest degree will be added first
    std::sort(polynomials.begin(), polynomials.end());

    for(Polynomials::iterator it = polynomials.begin(); it != polynomials.end(); it++){
      mCAD.addPolynomial(*it);

      mCAD.project();
      mCAD.lift();

      if(isProjectionDefinable()) {
        break;
      }
    }

    computeTruthValues();
  }

  void QE::simplifyCAD() {
    std::vector<carl::tree<smtrat::cad::Sample>::iterator> truthBoundaryCells;

    // level k
    for(auto it = mCAD.getLifting().getTree().begin_depth(k); it != mCAD.getLifting().getTree().end_depth(); it++) {
      if(it->isRoot()) {
        carl::tree<smtrat::cad::Sample>::iterator c = it;
        carl::tree<smtrat::cad::Sample>::iterator b = it.previous();
        carl::tree<smtrat::cad::Sample>::iterator d = it.next().next();

        if(mTruth.find(b)->second != mTruth.find(c)->second || mTruth.find(c)->second != mTruth.find(d)->second) {
          SMTRAT_LOG_DEBUG("smtrat.qe", mCAD.getLifting().extractSampleMap(c) << " is a truth-boundary cell");
          truthBoundaryCells.push_back(c);
        }
      }
    }
    std::vector<Polynomials> S;
    for(auto it = truthBoundaryCells.begin(); it != truthBoundaryCells.end(); it++) {
      Polynomials P;
      std::size_t numberOfProjectionFactors = mCAD.getProjection().size(n + 1 - k);
      for(int id = 0; id < numberOfProjectionFactors; id++) {
        if(mCAD.getProjection().hasPolynomialById(n + 1 - k, id)) {
          Polynomial p = (Polynomial) mCAD.getProjection().getPolynomialById(n + 1 - k, id);
          if(carl::Sign::ZERO == carl::sgn(carl::RealAlgebraicNumberEvaluation::evaluate(p, mCAD.getLifting().extractSampleMap(*it)))) {
            P.push_back(p);
          }
        }
      }
      if(!P.empty()) {
        S.push_back(P);
      }
    }
    if(!S.empty()) {
      Polynomials H = computeHittingSet(S);
      std::size_t numberOfProjectionFactors = mCAD.getProjection().size(n + 1 - k);
      for(int id = 0; id < numberOfProjectionFactors; id++) {
        if(mCAD.getProjection().hasPolynomialById(n + 1 - k, id)) {
          Polynomial p = (Polynomial) mCAD.getProjection().getPolynomialById(n + 1 - k, id);
          if(std::find(H.begin(), H.end(), p) == H.end()) {
            SMTRAT_LOG_DEBUG("smtrat.qe", "Remove " << p);
            mCAD.removePolynomial(n + 1 - k , id);
          }
        }
      }
      H.clear();
    }
    computeTruthValues();

    // level k-1 and below
    truthBoundaryCells.clear();
    S.clear();

    for(int i = k - 1; i > 0; i--) {
      Polynomials N;
      std::size_t numberOfProjectionFactors = mCAD.getProjection().size(n + 1 - i);
      for(int id = 0; id < numberOfProjectionFactors; id++) {
        if(mCAD.getProjection().hasPolynomialById(n + 1 - i, id)) {
          if(mCAD.getProjection().testProjectionFactor(n + 1 - i , id)) {
            N.push_back((Polynomial) mCAD.getProjection().getPolynomialById(n + 1 - i, id));
          }
        }
      }
      for(auto it = mCAD.getLifting().getTree().begin_depth(i); it != mCAD.getLifting().getTree().end_depth(); it++) {
        if(it->isRoot()) {
          carl::tree<smtrat::cad::Sample>::iterator c = it;
          carl::tree<smtrat::cad::Sample>::iterator b = it.previous();
          carl::tree<smtrat::cad::Sample>::iterator d = it.next().next();
          if(truthBoundaryTest(b,c,d)) {
            SMTRAT_LOG_DEBUG("smtrat.qe", mCAD.getLifting().extractSampleMap(c) << " is a truth-boundary cell");
            truthBoundaryCells.push_back(c);
          }
        }
      }
      for(auto it = truthBoundaryCells.begin(); it != truthBoundaryCells.end(); it++) {
        Polynomials P;
        for(int id = 0; id < numberOfProjectionFactors; id++) {
          if(mCAD.getProjection().hasPolynomialById(n + 1 - i, id)) {
            Polynomial p = (Polynomial) mCAD.getProjection().getPolynomialById(n + 1 - i, id);
            if(carl::Sign::ZERO == carl::sgn(carl::RealAlgebraicNumberEvaluation::evaluate(p, mCAD.getLifting().extractSampleMap(*it)))) {
              P.push_back(p);
            }
          }
        }
        if(!P.empty()) {
          S.push_back(P);
        }
      }
      if(!S.empty()) {
        Polynomials H = computeHittingSet(S);
        for(int id = 0; id < numberOfProjectionFactors; id++) {
          if(mCAD.getProjection().hasPolynomialById(n + 1 - i, id)) {
            Polynomial p = (Polynomial) mCAD.getProjection().getPolynomialById(n + 1 - i, id);
            if(std::find(N.begin(), N.end(), p) == N.end() && std::find(H.begin(), H.end(), p) == H.end()) {
              SMTRAT_LOG_DEBUG("smtrat.qe", "Remove " << p);
              mCAD.removePolynomial(n + 1 - i, id);
            }
          }
        }
        H.clear();
      }
      truthBoundaryCells.clear();
      S.clear();
    }
    computeTruthValues();
  }

  bool QE::truthBoundaryTest(carl::tree<smtrat::cad::Sample>::iterator& b, carl::tree<smtrat::cad::Sample>::iterator& c, carl::tree<smtrat::cad::Sample>::iterator& d) {
    std::vector<carl::tree<smtrat::cad::Sample>::iterator> children_b;
    std::vector<carl::tree<smtrat::cad::Sample>::iterator> children_c;
    std::vector<carl::tree<smtrat::cad::Sample>::iterator> children_d;
    for(auto child = mCAD.getLifting().getTree().begin_children(b); child != mCAD.getLifting().getTree().end_children(b); child++) {
      children_b.push_back(child);
    }
    for(auto child = mCAD.getLifting().getTree().begin_children(c); child != mCAD.getLifting().getTree().end_children(c); child++) {
      children_c.push_back(child);
    }
    for(auto child = mCAD.getLifting().getTree().begin_children(d); child != mCAD.getLifting().getTree().end_children(d); child++) {
      children_d.push_back(child);
    }

    if(mCAD.getLifting().getTree().max_depth(c) == k-1) {
      if(children_b.size() == children_c.size() && children_c.size() == children_d.size()) {
        for(int i = 0; i < children_c.size(); i++) {
          if(mTruth.find(children_b[i])->second != mTruth.find(children_c[i])->second || mTruth.find(children_c[i])->second != mTruth.find(std::next(children_d[i]))->second) {
            return true;
          }
        }
      }
    }else {
      if(children_b.size() == children_c.size() && children_c.size() == children_d.size()) {
        for(int i = 0; i < children_c.size(); i++) {
          if(truthBoundaryTest(children_b[i], children_c[i], children_d[i])) {
            return true;
          }
        }
      }
    }
    return false;
  }

  void QE::computeTruthValues() {
    mTruth.clear();

    // level n
    for(auto it = mCAD.getLifting().getTree().begin_leaf(); it != mCAD.getLifting().getTree().end_leaf(); it++) {
      Assignment assignment = mCAD.getLifting().extractSampleMap(it);
      carl::Model<Rational, Polynomial> model;
      for(const auto& a : assignment) {
        model.emplace(a.first, a.second);
      }
      bool truthValue = carl::model::evaluate(mQuantifierFreePart, model).asBool();
      mTruth.emplace(it, truthValue);
    }

    // level n-1 down to level k
    int i = n-1;
    for(auto quantifier = mQuantifiers.rbegin(); quantifier != mQuantifiers.rend(); quantifier++) {
      for(auto it = mCAD.getLifting().getTree().begin_depth(i); it != mCAD.getLifting().getTree().end_depth(); it++) {
        if(quantifier->second == smtrat::QuantifierType::EXISTS) {
          bool truthValue = false;
          for(auto child = mCAD.getLifting().getTree().begin_children(it); child != mCAD.getLifting().getTree().end_children(it); child++) {
            truthValue = truthValue || mTruth.find(child)->second;
          }
          mTruth.emplace(it, truthValue);
        }
        if(quantifier->second == smtrat::QuantifierType::FORALL) {
          bool truthValue = true;
          for(auto child = mCAD.getLifting().getTree().begin_children(it); child != mCAD.getLifting().getTree().end_children(it); child++) {
            truthValue = truthValue && mTruth.find(child)->second;
          }
          mTruth.emplace(it, truthValue);
        }
      }
      i = i-1;
    }
  }

  void QE::computeSignatures() {
    mSignature.clear();

    Assignment assignment;
    std::vector<carl::Sign> signature;
    for(auto it = mCAD.getLifting().getTree().begin_depth(k); it != mCAD.getLifting().getTree().end_depth(); it++) {
      assignment = mCAD.getLifting().extractSampleMap(it);
      carl::Model<Rational, Polynomial> model;
      for(const auto& a : assignment) {
        model.emplace(a.first, a.second);
      }
      for(int i = 1; i <= k; i++) {
        std::size_t numberOfProjectionFactors = mCAD.getProjection().size(n + 1 - i);
        for(int id = 0; id < numberOfProjectionFactors; id++) {
          if(mCAD.getProjection().hasPolynomialById(n + 1 - i, id)) {
            signature.push_back(carl::sgn(carl::RealAlgebraicNumberEvaluation::evaluate((Polynomial) mCAD.getProjection().getPolynomialById(n + 1 - i, id), assignment)));
          }
        }
      }
      mSignature.emplace(it, signature);

      assignment.clear();
      signature.clear();
    }
  }

  // helper to swap a key-value pair of a map
  template<typename key, typename value>
  std::pair<value, key> flip_pair(const std::pair<key, value> & p) {
    return std::pair<value, key>(p.second, p.first);
  }

  // helper to swap the keys and values of a map
  template<typename key, typename value>
  std::multimap<value, key> flip_map(const std::map<key, value> &src) {
    std::multimap<value, key> dst;
    std::transform(src.begin(), src.end(), std::inserter(dst, dst.begin()), flip_pair<key, value>);
    return dst;
  }

  bool QE::isProjectionDefinable() {
    mCauseConflict.clear();

    bool projectionDefinable = true;
    std::vector<carl::tree<smtrat::cad::Sample>::iterator> samplesOfSameSignature;

    computeSignatures();
    std::multimap<std::vector<carl::Sign>, carl::tree<smtrat::cad::Sample>::iterator> signature_flipped = flip_map(mSignature);
    std::vector<carl::Sign> signature = signature_flipped.begin()->first;

    for(auto it = signature_flipped.begin(); it != signature_flipped.end(); it++) {
      if(signature == it->first) {
        samplesOfSameSignature.push_back(it->second);
      }else{
        for(auto a = samplesOfSameSignature.begin(); a != samplesOfSameSignature.end(); a++) {
          for(auto b = std::next(a); b != samplesOfSameSignature.end(); b++) {
            if(mTruth.find(*a)->second != mTruth.find(*b)->second) {
              mCauseConflict.push_back(std::make_pair(*a,*b));
              projectionDefinable = false;
            }
          }
        }
        samplesOfSameSignature.clear();
        samplesOfSameSignature.push_back(it->second);

        signature.clear();
        signature = it->first;
      }
    }
    return projectionDefinable;
  }

  void QE::makeProjectionDefinable() {
    for(int i = k; i >= 1; i--) {
      std::vector<std::pair<carl::tree<smtrat::cad::Sample>::iterator,carl::tree<smtrat::cad::Sample>::iterator>> conflictingPairs;
      for(auto pair = mCauseConflict.begin(); pair != mCauseConflict.end(); pair++) {
        carl::tree<smtrat::cad::Sample>::iterator a = pair->first;
        carl::tree<smtrat::cad::Sample>::iterator b = pair->second;
        bool equals = false;
        for(int level = k; level > i; level--) {
          a = mCAD.getLifting().getTree().get_parent(a);
          b = mCAD.getLifting().getTree().get_parent(b);
          if(a == b) {
            equals = true;
          }
        }
        if(!equals) {
          if(mCAD.getLifting().getTree().get_parent(a) == mCAD.getLifting().getTree().get_parent(b)) {
            if(*a < *b) {
              conflictingPairs.push_back(std::make_pair(a,b));
            }else {
              conflictingPairs.push_back(std::make_pair(b,a));
            }
          }
        }
      }

      std::vector<carl::UnivariatePolynomial<Polynomial>> setOfProjectionFactors;
      std::vector<std::vector<carl::UnivariatePolynomial<Polynomial>>> setOfSetOfProjectionFactors;
      for(auto conflictingPair = conflictingPairs.begin(); conflictingPair != conflictingPairs.end(); conflictingPair++) {
        std::size_t numberOfProjectionFactors = mCAD.getProjection().size(n + 1 - i);
        for(int id = 0; id < numberOfProjectionFactors; id++) {
          if(mCAD.getProjection().hasPolynomialById(n + 1 - i, id)) {
            bool zeroInSomeCell = false, vanish = true;
            carl::UnivariatePolynomial<Polynomial> projectionFactor = mCAD.getProjection().getPolynomialById(n + 1 - i, id);
            carl::tree<smtrat::cad::Sample>::iterator it = conflictingPair->second;
            while(*conflictingPair->first < *it) {
              if(carl::Sign::ZERO == carl::sgn(carl::RealAlgebraicNumberEvaluation::evaluate((Polynomial) projectionFactor, mCAD.getLifting().extractSampleMap(it)))) {
                zeroInSomeCell = true;
              }else {
                vanish = false;
              }
              it = mCAD.getLifting().getTree().left_sibling(it);
            }
            if(vanish) {
              for(auto child = mCAD.getLifting().getTree().begin_children(mCAD.getLifting().getTree().get_parent(conflictingPair->first)); child != mCAD.getLifting().getTree().end_children(mCAD.getLifting().getTree().get_parent(conflictingPair->first)); child++) {
                if(carl::Sign::ZERO != carl::sgn(carl::RealAlgebraicNumberEvaluation::evaluate((Polynomial) projectionFactor, mCAD.getLifting().extractSampleMap(child)))) {
                  vanish = false;
                }
              }
            }
            if(zeroInSomeCell && !vanish) {
              setOfProjectionFactors.push_back(projectionFactor);
            }
          }
        }
        if(setOfProjectionFactors.size() != 0) {
          setOfSetOfProjectionFactors.push_back(setOfProjectionFactors);
          setOfProjectionFactors.clear();
        }
      }
      std::vector<carl::UnivariatePolynomial<Polynomial>> hittingSet = computeHittingSet(setOfSetOfProjectionFactors);

      Polynomials addToCAD;
      for(auto p = hittingSet.begin(); p != hittingSet.end(); p++) {
        for(uint nth = 0; nth <= p->degree(); nth++) {
          Polynomial nthDerivative = (Polynomial) p->derivative(nth);
          auto factorizationOfTheDerivative = carl::factorization(nthDerivative, false);

          for(auto factor = factorizationOfTheDerivative.begin(); factor != factorizationOfTheDerivative.end(); factor++) {
            addToCAD.push_back(factor->first);
          }
        }
      }

      for(const auto p : addToCAD) {
        SMTRAT_LOG_DEBUG("smtrat.qe", "Add " << p);
      }

      updateCAD(addToCAD);

      // if projection-definability is already achieved, we are done
      if(isProjectionDefinable()) {
        SMTRAT_LOG_DEBUG("smtrat.qe", "The CAD is now projection-definable");
        break;
      }else {
        SMTRAT_LOG_DEBUG("smtrat.qe", "The CAD is still not projection-definable");
      }
    }
  }

  Formula QE::constructImplicant(const carl::tree<smtrat::cad::Sample>::iterator& sample) {
    Assignment assignment;
    carl::Model<Rational, Polynomial> model;
    assignment = mCAD.getLifting().extractSampleMap(sample);
    for(const auto& a : assignment) {
      model.emplace(a.first, a.second);
    }
    Formulas L;
    for(const auto& atomicFormula : mAtomicFormulas) {
      if(carl::model::evaluate(atomicFormula, model).asBool()) {
        L.push_back(atomicFormula);
      }
    }

    assignment.clear();
    model.clear();
    Formulas evaluatedToFalse;
    std::vector<Formulas> S;
    for(const auto& falseSample : mFalseSamples) {
      assignment = mCAD.getLifting().extractSampleMap(falseSample);
      for(const auto& a : assignment) {
        model.emplace(a.first, a.second);
      }
      for(const auto& atomicFormula : L) {
        if(!carl::model::evaluate(atomicFormula, model).asBool()) {
          evaluatedToFalse.push_back(atomicFormula);
        }
      }
      assignment.clear();
      model.clear();
      if(!evaluatedToFalse.empty()) {
        S.push_back(evaluatedToFalse);
        evaluatedToFalse.clear();
      }
    }

    Formulas H = computeHittingSet(S);
    SMTRAT_LOG_DEBUG("smtrat.qe", Formula(carl::FormulaType::AND, H) << " is an implicant capturing " << mCAD.getLifting().extractSampleMap(sample));
    return Formula(carl::FormulaType::AND, H);
  }

  Formula QE::constructSolutionFormula() {
    for(auto sample_iterator = mCAD.getLifting().getTree().begin_depth(k); sample_iterator != mCAD.getLifting().getTree().end_depth(); sample_iterator++) {
      if(mTruth.find(sample_iterator)->second) {
        mTrueSamples.push_back(sample_iterator);
      }else {
        mFalseSamples.push_back(sample_iterator);
      }
    }
    for(int level = 1; level <= k; level++) {
      std::size_t numberOfProjectionFactors = mCAD.getProjection().size(n + 1 - level);
      for(int id = 0; id < numberOfProjectionFactors; id++) {
        if(mCAD.getProjection().hasPolynomialById(n + 1 - level, id)) {
          Polynomial p = (Polynomial) mCAD.getProjection().getPolynomialById(n + 1 - level, id);
          mAtomicFormulas.push_back(Formula(Constraint(p, carl::Relation::EQ)));
          mAtomicFormulas.push_back(Formula(Constraint(p, carl::Relation::NEQ)));
          mAtomicFormulas.push_back(Formula(Constraint(p, carl::Relation::LESS)));
          mAtomicFormulas.push_back(Formula(Constraint(p, carl::Relation::LEQ)));
          mAtomicFormulas.push_back(Formula(Constraint(p, carl::Relation::GREATER)));
          mAtomicFormulas.push_back(Formula(Constraint(p, carl::Relation::GEQ)));
        }
      }
    }

    Formulas implicants;
    bool captured = false;
    for(auto const& sample : mTrueSamples) {
      Assignment assignment = mCAD.getLifting().extractSampleMap(sample);
      carl::Model<Rational, Polynomial> model;
      for(const auto& a : assignment) {
        model.emplace(a.first, a.second);
      }
      for(auto const& implicant : implicants) {
        if(carl::model::evaluate(implicant, model).asBool()) {
          captured = true;
        }
      }
      if(!captured) {
        Formula implicant = constructImplicant(sample);
        implicants.push_back(implicant);
      }
      captured = false;
    }

    Formulas i;
    std::vector<Formulas> I;
    for(auto const& sample : mTrueSamples) {
      Assignment assignment = mCAD.getLifting().extractSampleMap(sample);
      carl::Model<Rational, Polynomial> model;
      for(const auto& a : assignment) {
        model.emplace(a.first, a.second);
      }
      for(auto const& implicant : implicants) {
        if(carl::model::evaluate(implicant, model).asBool()) {
          i.push_back(implicant);
        }
      }
      if(!i.empty()) {
        I.push_back(i);
        i.clear();
      }
    }

    Formulas H = computeHittingSet(I);
    return Formula(carl::FormulaType::OR, H);
  }

  template<typename T>
  std::vector<T> QE::computeHittingSet(const std::vector<std::vector<T>>& setOfSets) {
    std::vector<std::vector<T>> SoS;
    for(auto set = setOfSets.begin(); set != setOfSets.end(); set++) {
      SoS.push_back(*set);
    }

    std::vector<T> H;
    std::map<T, int> U;

    for(auto set = SoS.begin(); set != SoS.end(); set++) {
      for(auto element = set->begin(); element != set->end(); element++) {
        if(U.find(*element) != U.end()) {
          U.find(*element)->second++;
        }else {
          U.emplace(*element,1);
        }
      }
    }

    while(!SoS.empty()) {
      auto max = U.begin();
      for(auto it = U.begin(); it != U.end(); it++) {
        if(it->second > max->second) {
          max = it;
        }
      }
      H.push_back(max->first);
      for(auto set = SoS.begin(); set != SoS.end();) {
        if(std::find(set->begin(), set->end(), max->first) != set->end()) {
          set = SoS.erase(set);
        }else {
          set++;
        }
      }
      U.erase(max);
      if(!U.empty()) {
        for(auto it = U.begin(); it != U.end(); it++) {
          it->second = 0;
        }
        for(auto set = SoS.begin(); set != SoS.end(); set++) {
          for(auto element = set->begin(); element != set->end(); element++) {
            if(U.find(*element) != U.end()) {
              U.find(*element)->second++;
            }
          }
        }
      }
    }

    return H;
  }

} // End of namespace qe
} // End of namespace smtrat
