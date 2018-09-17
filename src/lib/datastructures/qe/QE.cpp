#include "QE.h"

namespace smtrat{
namespace qe{

////////////////////////////////////////////////////////////////////////////////
// Public //////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

  QE::QE(Formula &quantifierFreePart, std::map<Variable, smtrat::parser::QuantifierType>& quantifiers) {
    /*
    * Informationen aus den uebergebenen Daten extrahieren
    * - Der Quantifier-free Part
    * - Die Variablen
    * - Die Constraints
    * - Die Quantoren
    * - Anzahl der Variablen n
    * - Anzahl der freien Variablen k
    */

    //std::cout << "------------------------------------------------------------------------" << std::endl;
    //std::cout << "Informationen aus den uebergebenen Daten extrahieren." << std::endl;
    //std::cout << std::endl;

    // Quantifier-free part ////////////////////////////////////////////////////
    mQuantifierFreePart = quantifierFreePart;

    // AUSGABE: Quantifier-free part
    //std::cout << "Quantifier-free part: " << mQuantifierFreePart << std::endl;

    // Quantoren ///////////////////////////////////////////////////////////////
    mQuantifiers = quantifiers;

    //std::cout << "Quantoren: ";
    for(auto it = mQuantifiers.begin(); it != mQuantifiers.end(); it++) {
      if(it->second == smtrat::parser::QuantifierType::EXISTS) {
        //std::cout << "E " << it->first << " ";
      }else {
        //std::cout << "A " << it->first << " ";
      }
    }
    //std::cout << std::endl;

    // Quantifizierte Variablen ////////////////////////////////////////////////
    for(auto it = mQuantifiers.rbegin(); it != mQuantifiers.rend(); it++) {
      mVariables.push_back(it->first);
    }

    // Freie Variablen ///////////////////////////////////////////////////////////////
    std::set<Variable> variables_as_set = mQuantifierFreePart.variables();

		// Die Menge der Variablen in einen Vector umwandeln
		for(carl::Variables::iterator it = variables_as_set.begin(); it != variables_as_set.end(); it++){
      if(std::find(mVariables.begin(), mVariables.end(), *it) == mVariables.end()) {
        mVariables.push_back(*it);
      }
		}

    // AUSGABE: Menge der Variablen
    //std::cout << "Variablen: ";
    for(Variables::iterator it = mVariables.begin(); it != mVariables.end(); it++){
			//std::cout << (*it) << " ";
		}
    //std::cout << std::endl;

    // Anzahl der Variablen n //////////////////////////////////////////////////
    n = mVariables.size();

    // Anzahl der freien Variablen k ///////////////////////////////////////////
    k = mVariables.size() - mQuantifiers.size();

    // Constraints /////////////////////////////////////////////////////////////
    mQuantifierFreePart.getConstraints(mConstraints);

    // AUSGABE: Menge der Constraints
    //std::cout << "Constraints: ";
    for(Constraints::iterator it = mConstraints.begin(); it != mConstraints.end(); it++){
			//std::cout << (*it) << " ";
		}
    //std::cout << std::endl;
    //std::cout << std::endl;
  }

  Formula QE::eliminateQuantifiers() {
    constructCAD();

    computeTruthValues();

    simplifyCAD();

    if(!isProjectionDefinable()) {
      makeProjectionDefinable();
    }

    return constructSolutionFormula();
  }

////////////////////////////////////////////////////////////////////////////////
// Private /////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

  void QE::constructCAD() {
    /*
    * CAD bauen
    * - CAD initialisieren
    * - Constraints hinzufuegen
    * - Projektion berechnen
    * - LiftingTree berechnen
    */

    //std::cout << "------------------------------------------------------------------------" << std::endl;
    //std::cout << "CAD bauen." << std::endl;
    //std::cout << std::endl;

    // CAD initialisieren //////////////////////////////////////////////////////
    mCAD.reset(mVariables);

    // Constraints hinzufuegen /////////////////////////////////////////////////
    for(Constraints::iterator it = mConstraints.begin(); it != mConstraints.end(); it++) {
      mCAD.addConstraint(*it);
    }

    // Projektion berechnen ////////////////////////////////////////////////////

    /* Anmerkung:
    * - CADSettings erbt im wesentlichen alle Einstellungen von BaseSettings
    * - BaseSettings sind so konfiguriert, dass Constraints beim Hinzufueegen projeziert werden
    * - An diesem Punkt haben wir also schon die Projektion
    */

    // AUSGABE: Projektion
    //std::cout << "Projection: " << std::endl;
    std::cout << mCAD.getProjection() << std::endl;


    // LiftingTree berechnen ///////////////////////////////////////////////////

    mCAD.lift();

    // AUSGABE: LiftingTree
    //std::cout << "LiftingTree: " << std::endl;
    std::cout << mCAD.getLifting().getTree() << std::endl;
  }

  void QE::updateCAD(Constraints& constraints) {
    /*
    * CAD updaten
    * - Die neuen Constraints hinzufuegen
    * - Constraints einzeln hinzufuegen
    * - nach Hinzufuegen eines einzelnen auf projection definability testen
    * - Projektion neu berechnen
    * - LiftingTree neu berechnen
    */

    //std::cout << "------------------------------------------------------------------------" << std::endl;
    //std::cout << "CAD updaten. " << std::endl;
    //std::cout << std::endl;

    // Die Constraints sortieren, sodass solche mit kleineren Grad zuerst hinzugefuegt werden
    // Anmerkung: Das is ein sort mit lambda-Ausdruck
    std::sort(constraints.begin(), constraints.end(), [] (const auto& lhs, const auto& rhs) {return lhs.maxDegree() < rhs.maxDegree();});

    // Die neuen Constraints hinzufuegen und Projektion neu berechnen
    for(Constraints::iterator it = constraints.begin(); it != constraints.end(); it++){
      // TODO: Nur wirklich neue Constraints hinzufuegen
      mCAD.addConstraint(*it);

      // AUSGABE: Projektion
      //std::cout << "Projection: " << std::endl;
      //std::cout << mCAD.getProjection() << std::endl;

      // LiftingTree neu berechnen
      mCAD.lift();

      // AUSGABE: LiftingTree
      //std::cout << "LiftingTree: " << std::endl;
      //std::cout << mCAD.getLifting().getTree() << std::endl;

      if(isProjectionDefinable()) {
        break;
      }
    }
  }

  void QE::simplifyCAD() {
    //std::cout << "Simplify the CAD" << std::endl;

    //std::cout << "Level k" << std::endl;

    // Bestimme alle k-Level truth-boundary Zellen
    std::vector<carl::tree<smtrat::cad::Sample>::iterator> truthBoundaryCells;

    // Iteriere von der ersten bis zur vorvorletzten k-Level Zelle
    for(auto it = mCAD.getLifting().getTree().begin_depth(k); it != mCAD.getLifting().getTree().end_depth(); it++) {
      // Falls die Zelle eine section cell ist
      if(it->isRoot()) {
        carl::tree<smtrat::cad::Sample>::iterator c = it;
        carl::tree<smtrat::cad::Sample>::iterator b = it.previous();
        carl::tree<smtrat::cad::Sample>::iterator d = it.next().next();

        //std::cout << "Betrachtete Zellen: " << *b << ", " << *c << ", " << *d << std::endl;

        // Betrachte 3 benachbarte Zellen
        if(mTruth.find(b)->second != mTruth.find(c)->second || mTruth.find(c)->second != mTruth.find(d)->second) {
          // Die Zelle auf die std::next(it) zeigt ist eine truth-boundary Zelle
          truthBoundaryCells.push_back(c);
        }
      }
    }

    // Bestimme fuer jede k-Level truth-boundary Zelle die Menge der k-level Polynome die 0 in dieser Zelle sind
    std::vector<Polynomials> S;

    // Iteriere ueber alle k-Level truth-boundary Zellen
    for(auto it = truthBoundaryCells.begin(); it != truthBoundaryCells.end(); it++) {
      // Iteriere ueber alle k-Level Projektionsfaktoren
      Polynomials P;

      // Anzahl der k-Level Projektionsfaktoren bestimmen
      std::size_t numberOfProjectionFactors = mCAD.getProjection().size(n + 1 - k);

      // Ueber alle k-Level Projektionsfaktoren iterieren
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

    // Berechne ein HittingSet fuer S
    if(!S.empty()) {
      Polynomials H = computeHittingSet(S);

      // Loesche alle k-Level Projektionsfaktoren die in der Projektion aber nicht in H sind

      // Anzahl der k-Level Projektionsfaktoren bestimmen
      std::size_t numberOfProjectionFactors = mCAD.getProjection().size(n + 1 - k);

      // Ueber alle k-Level Projektionsfaktoren iterieren
      for(int id = 0; id < numberOfProjectionFactors; id++) {
        if(mCAD.getProjection().hasPolynomialById(n + 1 - k, id)) {
          Polynomial p = (Polynomial) mCAD.getProjection().getPolynomialById(n + 1 - k, id);

          // Der k-Level Projektionsfaktor ist nicht in H
          if(std::find(H.begin(), H.end(), p) == H.end()) {
            //std::cout << "Es wurde " << p << " geloescht." << std::endl;
            mCAD.removePolynomial(n + 1 - k , id);
          }
        }
      }

      H.clear();
    }

    // Reset fuer Level k-1 und darunter
    truthBoundaryCells.clear();
    S.clear();

    //std::cout << "Level k-1 und darunter:" << std::endl;

    // Weiter fuer Level k-1 und darunter
    for(int i = k - 1; i > 0; i--) {
      // Bestimme die Menge der i-level Projektionsfaktoren die nicht geloescht werden duerfen (da sonst die Abschlusseigenschaft unter Projektion verletzt waere)
      Polynomials N;

      // Anzahl der i-Level Projektionsfaktoren bestimmen
      std::size_t numberOfProjectionFactors = mCAD.getProjection().size(n + 1 - i);

      // Ueber alle k-Level Projektionsfaktoren iterieren
      for(int id = 0; id < numberOfProjectionFactors; id++) {
        if(mCAD.getProjection().hasPolynomialById(n + 1 - i, id)) {
          // Teste ob das Polynom nicht geloescht werden darf (da sonst die Abschlusseigenschaft unter Projektion verletzt waere)
          if(mCAD.getProjection().testPolynomial(n + 1 - i , id)) {
            N.push_back((Polynomial) mCAD.getProjection().getPolynomialById(n + 1 - i, id));
          }
        }
      }

      // Bestimme alle i-Level truth-boundary Zellen

      // Iteriere von der ersten bis zur vorvorletzten i-Level Zelle
      for(auto it = mCAD.getLifting().getTree().begin_depth(i); it != mCAD.getLifting().getTree().end_depth(); it++) {
        // Falls die Zelle eine section cell ist
        if(it->isRoot()) {
          carl::tree<smtrat::cad::Sample>::iterator c = it;
          carl::tree<smtrat::cad::Sample>::iterator b = it.previous();
          carl::tree<smtrat::cad::Sample>::iterator d = it.next().next();

          //std::cout << "Betrachtete Zellen: " << *b << ", " << *c << ", " << *d << std::endl;

          if(truthBoundaryTest(b,c,d)) {
            truthBoundaryCells.push_back(c);
          }
        }
      }

      // Bestimme fuer jede k-Level truth-boundary Zelle die Menge der k-level Polynome die 0 in dieser Zelle sind

      // Iteriere ueber alle k-Level truth-boundary Zellen
      for(auto it = truthBoundaryCells.begin(); it != truthBoundaryCells.end(); it++) {
        // Iteriere ueber alle k-Level Projektionsfaktoren
        Polynomials P;

        // Ueber alle k-Level Projektionsfaktoren iterieren
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
        // Berechne ein HittingSet fuer S
        Polynomials H = computeHittingSet(S);

        // Loesche alle i-Level Projektionsfaktoren die in der Projektion aber weder in N noch H sind

        // Ueber alle k-Level Projektionsfaktoren iterieren
        for(int id = 0; id < numberOfProjectionFactors; id++) {
          if(mCAD.getProjection().hasPolynomialById(n + 1 - i, id)) {
            Polynomial p = (Polynomial) mCAD.getProjection().getPolynomialById(n + 1 - i, id);

            // Der i-Level Projektionsfaktor ist weder in N noch in H
            if(std::find(N.begin(), N.end(), p) == N.end() && std::find(H.begin(), H.end(), p) == H.end()) {
              //std::cout << "Es wurde " << p << " geloescht." << std::endl;
              mCAD.removePolynomial(n + 1 - i, id);
            }
          }
        }

        H.clear();
      }

      // Reset fuer die naechste Iteration
      truthBoundaryCells.clear();
      S.clear();
    }
  }

  bool QE::truthBoundaryTest(carl::tree<smtrat::cad::Sample>::iterator& b, carl::tree<smtrat::cad::Sample>::iterator& c, carl::tree<smtrat::cad::Sample>::iterator& d) {
    // Rekursionschritt: Auf das naechst hoehere Level
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

    // Rekursionsabbruch: Level k ist erreicht
    if(mCAD.getLifting().getTree().max_depth(c) == k-1) {
      // Falls die Stacks ueber b,c und d gleich viele Elemente haben
      if(children_b.size() == children_c.size() && children_c.size() == children_d.size()) {
        for(int i = 0; i < children_c.size(); i++) {
          // Wenn mindestens ein Tripel korrespondierender k-level Zellen in ihren Wahrheitswerten nicht uebereinstimmen haben wir ein truth boundary
          if(mTruth.find(children_b[i])->second != mTruth.find(children_c[i])->second || mTruth.find(children_c[i])->second != mTruth.find(std::next(children_d[i]))->second) {
            return true;
          }
        }
      }
    }else {
      // Falls die Stacks ueber b,c und d gleich viele Elemente haben
      if(children_b.size() == children_c.size() && children_c.size() == children_d.size()) {
        for(int i = 0; i < children_c.size(); i++) {
          // Rekursiver Aufruf
          if(truthBoundaryTest(children_b[i], children_c[i], children_d[i])) {
            return true;
          }
        }
      }
    }

    return false;
  }

  void QE::computeTruthValues() {
    /* Bestimmung der Wahrheitswerte aller n- bis k-Level CAD-Zellen
    * - Bestimmung der Wahrheitswerte der n-Level CAD-Zellen durch einsetzen in die Formel
    * - Rekursive Bestimmung der Wahrheitswerte der i-Level CAD-Zellen (mit k <= i < n)
    */

    // Reset mTruth
    mTruth.clear();

    //std::cout << "------------------------------------------------------------------------" << std::endl;
    //std::cout << "Wahrheitswerte aller n- bis k-Level CAD-Zellen bestimmen." << std::endl;
    //std::cout << std::endl;

    // Bestimmung der Wahrheitswerte der n-Level CAD-Zellen ////////////////////

    // AUSGABE: akutelles Level
    //std::cout << "Level: " << n << std::endl;
    //std::cout << std::endl;

    // Ueber die Blaetter des LiftingTree's iterieren
    for(auto it = mCAD.getLifting().getTree().begin_leaf(); it != mCAD.getLifting().getTree().end_leaf(); it++) {
      // Das Assignment des aktuell betrachteten Blattes aus dem LiftingTree extrahieren
      Assignment assignment = mCAD.getLifting().extractSampleMap(it);

      // Das Assignment in ein Model umwandeln
      carl::Model<Rational, Polynomial> model;
      for(const auto& a : assignment) {
        model.emplace(a.first, a.second);
      }

      // Wahrheitswert der CAD-Zelle durch einsetzen in die Formel bestimmen
      bool truthValue = carl::model::evaluate(mQuantifierFreePart, model).asBool();

      // CAD-Zelle, repraesentiert durch einen Sample-Tree-Iterator, und zugehoerigen Wahrheitswert speichern
      mTruth.emplace(it, truthValue);

      // AUSGABE: CAD-Zelle und zugehoeriger Wahrheitswert
      //std::cout << assignment << ": " << ((truthValue == 0) ? "FALSE" : "TRUE") << std::endl;
    }

    // Bestimmung der Wahrheitswerte der i-Level CAD-Zellen ////////////////////

    int i = n-1;

    // Ueber die Quantoren iterieren
    for(const auto& quantifier : mQuantifiers) {
      // AUSGABE: akutelles Level
      //std::cout << std::endl;
      //std::cout << "Level: " << i << std::endl;
      //std::cout << std::endl;

      // Ueber die Knoten der Tiefe i des LiftingTree's iterieren
      for(auto it = mCAD.getLifting().getTree().begin_depth(i); it != mCAD.getLifting().getTree().end_depth(); it++) {
        // Der Fall das x_i durch einen Existenzquantor quantifiziert wird
        if(quantifier.second == smtrat::parser::QuantifierType::EXISTS) {
          bool truthValue = false;

          // Die Wahrheitswerte aller zugehoeriger i+1-Level Zellen betrachten
          for(auto child = mCAD.getLifting().getTree().begin_children(it); child != mCAD.getLifting().getTree().end_children(it); child++) {
            truthValue = truthValue || mTruth.find(child)->second;
          }

          // CAD-Zelle, repraesentiert durch einen Sample-Tree-Iterator, und zugehoerigen Wahrheitswert speichern
          mTruth.emplace(it, truthValue);

          // AUSGABE: CAD-Zelle und zugehoeriger Wahrheitswert
          //std::cout << mCAD.getLifting().extractSampleMap(it) << ": " << ((truthValue == 0) ? "FALSE" : "TRUE") << std::endl;
        }

        // Der Fall das x_i durch einen Existenzquantor quantifiziert wird
        if(quantifier.second == smtrat::parser::QuantifierType::FORALL) {
          bool truthValue = true;

          // Die Wahrheitswerte aller zugehoeriger i+1-Level Zellen betrachten
          for(auto child = mCAD.getLifting().getTree().begin_children(it); child != mCAD.getLifting().getTree().end_children(it); child++) {
            truthValue = truthValue && mTruth.find(child)->second;
          }

          // CAD-Zelle, repraesentiert durch einen Sample-Tree-Iterator, und zugehoerigen Wahrheitswert speichern
          mTruth.emplace(it, truthValue);

          // AUSGABE: CAD-Zelle und zugehoeriger Wahrheitswert
          //std::cout << mCAD.getLifting().extractSampleMap(it) << ": " << ((truthValue == 0) ? "FALSE" : "TRUE") << std::endl;
        }
      }

      i = i-1;
    }
    //std::cout << std::endl;
  }

  void QE::computeSignatures() {
    /* Bestimmung der Signaturen aller k-Level CAD-Zellen
    * - Ueber alle k-Level CAD-Zellen iterieren
    * - Fuer jede Zelle ueber alle 1- bis k-Level Projektionsfaktoren iterieren
    * - In jeden Faktor das die Zelle repraesentierende Sample einsetzen und Sign bestimmen
    */

    // Reset mSignature
    mSignature.clear();

    //std::cout << "Signaturen aller " << k << "-Level CAD-Zellen bestimmen. " << std::endl;
    //std::cout << std::endl;

    Assignment assignment;
    std::vector<carl::Sign> signature;

    // Ueber alle k-Level CAD-Zellen iterieren /////////////////////////////////
    for(auto it = mCAD.getLifting().getTree().begin_depth(k); it != mCAD.getLifting().getTree().end_depth(); it++) {
      // Assignment der Zelle bestimmen
      assignment = mCAD.getLifting().extractSampleMap(it);

      // Das Assignment in ein Model umwandeln
      carl::Model<Rational, Polynomial> model;
      for(const auto& a : assignment) {
        model.emplace(a.first, a.second);
      }

      // Fuer jede Zelle ueber alle 1- bis k-Level Projektionsfaktoren iterieren
      for(int i = 1; i <= k; i++) {
        // WICHTIG: Level muss fuer Projektionsfaktoren korrigiert werden

        // Anzahl der i-Level Projektionsfaktoren bestimmen
        std::size_t numberOfProjectionFactors = mCAD.getProjection().size(n + 1 - i);

        // Ueber alle i-Level Projektionsfaktoren iterieren ////////////////////
        for(int id = 0; id < numberOfProjectionFactors; id++) {
          if(mCAD.getProjection().hasPolynomialById(n + 1 - i, id)) {
            // In jeden Faktor das die Zelle repraesentierende Assignment einsetzen
            signature.push_back(carl::sgn(carl::RealAlgebraicNumberEvaluation::evaluate((Polynomial) mCAD.getProjection().getPolynomialById(n + 1 - i, id), assignment)));
          }
        }
      }

      // CAD-Zelle, repraesentiert durch einen Sample-Tree-Iterator, und zugehoerige Signature speichern
      mSignature.emplace(it, signature);

      // Assignment zuruecksetzen
      assignment.clear();
      // Signatur zuruecksetzen
      signature.clear();
    }
  }

  // Hilfsfunktion um ein Schluessel-Werte Paar einer Map zu tauschen
  template<typename key, typename value>
  std::pair<value, key> flip_pair(const std::pair<key, value> & p) {
    return std::pair<value, key>(p.second, p.first);
  }

  // Hilfsfunktion um Schluessel und Werte einer Map zu tauschen
  template<typename key, typename value>
  std::multimap<value, key> flip_map(const std::map<key, value> &src) {
    std::multimap<value, key> dst;
    std::transform(src.begin(), src.end(), std::inserter(dst, dst.begin()), flip_pair<key, value>);
    return dst;
  }

  bool QE::isProjectionDefinable() {
    /* Bestimmung der Signaturen aller k-Level CAD-Zellen
    * - Ueber alle k-Level CAD-Zellen iterieren
    * - Fuer jede Zelle ueber alle k-Level Projektionsfaktoren iterieren
    * - In jeden Faktor das die Zelle repraesentierende Sample einsetzen und Sign bestimmen
    */

    // Reset mCauseConflict
    mCauseConflict.clear();

    //std::cout << "------------------------------------------------------------------------" << std::endl;
    //std::cout << "Teste ob die konstruierte CAD projection definable ist. " << std::endl;
    //std::cout << std::endl;

    bool projectionDefinable = true;
    std::vector<carl::tree<smtrat::cad::Sample>::iterator> samplesOfSameSignature;

    // Um auf projection definability zu testen, muessen die Signaturen berechnet werden
    computeSignatures();

    // Die Datenstruktur, die die Signaturen der k-Level CAD-Zellen festhaelt nach Signatur sortieren
    std::multimap<std::vector<carl::Sign>, carl::tree<smtrat::cad::Sample>::iterator> signature_flipped = flip_map(mSignature);

    // Momentan betrachtete Signatur
    std::vector<carl::Sign> signature = signature_flipped.begin()->first;

    for(auto it = signature_flipped.begin(); it != signature_flipped.end(); it++) {
      // AUSGABE: CAD-Zelle, Signatur, Wahrheitswert
      //std::cout << mCAD.getLifting().extractSampleMap(it->second) << ": (";
      for(auto jt = it->first.begin(); jt != it->first.end(); jt++) {
        //std::cout << ((jt == it->first.begin()) ? "" : ", ") << (*jt);
      }
      //std::cout << ") , " << ((mTruth.find(it->second)->second == 0) ? "FALSE" : "TRUE") << std::endl;

      // Die Signatur hat sich nicht geaendert
      if(signature == it->first) {
        samplesOfSameSignature.push_back(it->second);

      // Die Signatur hat sich geandert
      }else{
        // Alle Paare durchgehen, um nach solchen zu suchen die Konflikte verursachen
        for(auto a = samplesOfSameSignature.begin(); a != samplesOfSameSignature.end(); a++) {
          for(auto b = std::next(a); b != samplesOfSameSignature.end(); b++) {
            // Das Paar hat die selbe Signatur, jedoch unterschiedliche Wahrheitswerte
            if(mTruth.find(*a)->second != mTruth.find(*b)->second) {
              mCauseConflict.push_back(std::make_pair(*a,*b));
              projectionDefinable = false;
            }
          }
        }

        // Den Vector der CAD-Zellen mit der selben Signatur resetten
        samplesOfSameSignature.clear();
        samplesOfSameSignature.push_back(it->second);

        // Momentan betrachtete Signatur reseten
        signature.clear();
        signature = it->first;
      }
    }
    //std::cout << std::endl;

    return projectionDefinable;
  }

  void QE::makeProjectionDefinable() {
    /* Die CAD manipulieren, sodass sie projection definable wird
    * - Entferne conflicting pairs beginnend mit Level k bis hin zu Level 1
    * - Bestimme Conflicting pairs des betrachteden Levels
    * - Fuer jedes confliting pair:
    * - Bestimme die Menge der Projektionsfaktoren:
    * - Die 1.) in einer CAD-Zelle zwischen den Zellen des conflicting pair zu 0 evaluiert werden
    * - und 2.) nicht identisch 0 sind
    * - Berechne ein Hitting Set all dieser Mengen von Projektionsfaktoren
    * - Berechne alle irreduziblen Faktoren aller partiellen Ableitungen der Polynome des Hitting Sets
    * - Konstruiere eine geupdatete CAD, durch hinzufuegen der neu ermittelten Projektionsfaktoren
    * - Die geupdatete CAD hat nun keine conflicting pairs des betrachteden Levels mehr
    */

    //std::cout << "------------------------------------------------------------------------" << std::endl;
    //std::cout << "Manipuliere die CAD, sodass sie projection definable wird. " << std::endl;
    //std::cout << std::endl;

    for(int i = k; i >= 1; i--) {
      //std::cout << "Entferne conflicting pairs in Level: " << i << ". " << std::endl;

      // 1.) Bestimme confliting pairs des entsprechenden Levels
      //std::cout << "Bestimme die Menge der conflicting pairs. " << std::endl;

      // Die Menge der conflicting pairs
      std::vector<std::pair<carl::tree<smtrat::cad::Sample>::iterator,carl::tree<smtrat::cad::Sample>::iterator>> conflictingPairs;

      // Alle konfliktverursachenden Zellenpaare durchgehen
      for(auto pair = mCauseConflict.begin(); pair != mCauseConflict.end(); pair++) {
        carl::tree<smtrat::cad::Sample>::iterator a = pair->first;
        carl::tree<smtrat::cad::Sample>::iterator b = pair->second;

        /* Anmerkung:
        * - Wir interessieren uns fuer die conflicting pairs des uebergebenen Levels
        * - Wir nehmen weiterhin an, dass keine conflicting pairs eines hoeheren Levels mehr existieren
        * - (sicherheitshalber testen wir aber dennoch danach)
        */

        // Um festzuhalten ob a und b bereits auf einem Level zwischen i und k im selben Stack liegen
        bool equals = false;

        // Projektion auf Level i der konfliktverursachenden Zellenpaare berechnen
        for(int level = k; level > i; level--) {
          a = mCAD.getLifting().getTree().get_parent(a);
          b = mCAD.getLifting().getTree().get_parent(b);

          // Falls a und b bereits auf einem Level zwischen i und k im selben Stack liegen, brauchen wir nicht weiter rechnen
          if(a == b) {
            equals = true;
          }
        }

        if(!equals) {
          // Auf Level i liegen die Projektionen der konfliktverursachenden Zellenpaare in einem Stack wenn deren Elternknoten gleich sind
          if(mCAD.getLifting().getTree().get_parent(a) == mCAD.getLifting().getTree().get_parent(b)) {
            // Sicherheitsmassnahme um Fehler beim Iterieren ueber den Stack zwischen einem conflicting pair zu verhindern
            if(*a < *b) {
              conflictingPairs.push_back(std::make_pair(a,b));
            }else {
              conflictingPairs.push_back(std::make_pair(b,a));
            }

            /*
            if(a < b) {
              if(!mCAD.getLifting().getTree().is_leftmost(b)) {
                conflictingPairs.push_back(std::make_pair(a,b));
              }
            }else {
              if(!mCAD.getLifting().getTree().is_leftmost(a)) {
                conflictingPairs.push_back(std::make_pair(b,a));
              }
            }
            */

          }
        }
      }

      // 2.) Bestimme die Menge der Mengen der zu betrachtenden Projektionsfaktoren
      //std::cout << "Bestimme die Menge der Mengen der zu betrachtenden Projektionsfaktoren. " << std::endl;

      // Die Menge der zu betrachtenden Projektionsfaktoren fuer ein confliting pair (a,b)
      std::vector<carl::UnivariatePolynomial<Polynomial>> setOfProjectionFactors;
      // Die Menge der Mengen der zu betrachtenden Projektionsfaktoren fuer alle conflicting pairs (a,b)
      std::vector<std::vector<carl::UnivariatePolynomial<Polynomial>>> setOfSetOfProjectionFactors;

      // Iteriere ueber alle conflicting pairs
      for(auto conflictingPair = conflictingPairs.begin(); conflictingPair != conflictingPairs.end(); conflictingPair++) {

        // Anzahl der i-Level Projektionsfaktoren bestimmen
        std::size_t numberOfProjectionFactors = mCAD.getProjection().size(n + 1 - i);

        // Iteriere ueber alle i-Level Projektionsfaktoren
        for(int id = 0; id < numberOfProjectionFactors; id++) {
          if(mCAD.getProjection().hasPolynomialById(n + 1 - i, id)) {
            bool zeroInSomeCell = false, vanish = true;

            // Hole den Projektionsfaktor zu gegebener id
            carl::UnivariatePolynomial<Polynomial> projectionFactor = mCAD.getProjection().getPolynomialById(n + 1 - i, id);

            // Startend in CAD-Zelle b immerzu den linken Geschwisterknoten betrachten, bis CAD-Zelle a erreicht ist
            carl::tree<smtrat::cad::Sample>::iterator it = conflictingPair->second;
            // (Zur Abbruchbedingung: a und b haben die selbe Signatur, es reicht also b zu betrachten)
            while(*conflictingPair->first < *it) {
              // Teste, ob der Projektionsfaktor in der CAD-Zelle zu 0 evaluiert wird
              if(carl::Sign::ZERO == carl::sgn(carl::RealAlgebraicNumberEvaluation::evaluate((Polynomial) projectionFactor, mCAD.getLifting().extractSampleMap(it)))) {
                zeroInSomeCell = true;
              }else {
                vanish = false;
              }

              // Die naechste CAD-Zelle (linke Geschwister Zelle) betrachten
              it = mCAD.getLifting().getTree().left_sibling(it);
            }

            // Falls wir noch nicht ausschliessen konnten dass der Projektionsfaktor im Stack identisch 0 ist, teste alle CAD-Zellen des Stacks
            if(vanish) {
              for(auto child = mCAD.getLifting().getTree().begin_children(mCAD.getLifting().getTree().get_parent(conflictingPair->first)); child != mCAD.getLifting().getTree().end_children(mCAD.getLifting().getTree().get_parent(conflictingPair->first)); child++) {
                if(carl::Sign::ZERO != carl::sgn(carl::RealAlgebraicNumberEvaluation::evaluate((Polynomial) projectionFactor, mCAD.getLifting().extractSampleMap(child)))) {
                  vanish = false;
                }
              }
            }

            // Projektionsfaktor zu der Menge der zu betrachtenden Projektionsfaktoren hinzufuegen,
            // falls 1.) der Projektionsfaktor zu 0 in einer der CAD-Zellen zwischen a und b evaluiert wurde
            // und 2.) der Projektionsfaktor nicht identisch 0 ist
            if(zeroInSomeCell && !vanish) {
              setOfProjectionFactors.push_back(projectionFactor);
            }
          }
        }

        // TODO: Zum Nachdenken: Wieso kann der Fall eintreten, dass die Menge der zu betrachtenden Projektionsfaktoren leer ist?
        if(setOfProjectionFactors.size() != 0) {
          // Die Menge der zu betrachtenden Projektionsfaktoren zu der Menge der Mengen hinzufuegen
          setOfSetOfProjectionFactors.push_back(setOfProjectionFactors);

          // Die Menge der zu betrachtenden Projektionsfaktoren resetten
          setOfProjectionFactors.clear();
        }
      }

      //std::cout << "Die Menge der Mengen der zu betrachtenden Projektionsfaktoren: " << std::endl;
      for(auto it = setOfSetOfProjectionFactors.begin(); it != setOfSetOfProjectionFactors.end(); it++) {
        for(auto jt = it->begin(); jt != it->end(); jt++) {
          //std::cout << *jt << std::endl;
        }
        //std::cout << std::endl;
      }

      // 3.) Berechne ein Hitting Set fuer die Menge der Mengen der zu betrachtenden Projektionsfaktoren
      //std::cout << "Berechne ein Hitting Set fuer die Menge der Mengen der zu betrachtenden Projektionsfaktoren. " << std::endl;

      std::vector<carl::UnivariatePolynomial<Polynomial>> hittingSet = computeHittingSet(setOfSetOfProjectionFactors);

      //std::cout << "Das Hitting Set der zu betrachteden Projektionsfaktoren: " << std::endl;
      for(auto it = hittingSet.begin(); it != hittingSet.end(); it++) {
        //std::cout << *it << std::endl;
      }

      // 4.) Berechne alle irreduziblen Faktoren aller partiellen Ableitungen (nach der Variable i-ten Levels)
      //std::cout << "Berechne alle irreduziblen Faktoren aller partiellen Ableitungen der Polynome des Hitting Sets. " << std::endl;

      // Menge der der CAD hinzuzufuegenden Constraints
      Constraints addToCAD;

      // Iteriere ueber alle Projektionsfaktoren des berechneten Hitting Sets
      for(auto p = hittingSet.begin(); p != hittingSet.end(); p++) {
        // Berechne alle partiellen Ableitungen von p (nach der Variable i-ten Levels)
        for(uint nth = 0; nth <= p->degree(); nth++) {
          Polynomial nthDerivative = (Polynomial) p->derivative(nth);
          // Fuege die irreduziblen Faktoren der partiellen Ableitung zur Menge der hinzuzufuegenden Projektionsfaktoren hinzu
          auto factorizationOfTheDerivative = carl::factorization(nthDerivative, false);

          for(auto factor = factorizationOfTheDerivative.begin(); factor != factorizationOfTheDerivative.end(); factor++) {
            addToCAD.push_back(Constraint(factor->first, carl::Relation::EQ));
          }
        }
      }

      //std::cout << "Die Menge der irreduziblen Faktoren aller partiellen Ableitungen: " << std::endl;
      for(auto it = addToCAD.begin(); it != addToCAD.end(); it++) {
        //std::cout << it->lhs() << std::endl;
      }

      // 5.) CAD updaten
      updateCAD(addToCAD);

      //std::cout << std::endl;

      /* Anmerkung:
      * - Falls die CAD jetzt projection definable ist kann abgebrochen werden
      * - Falls sie immernoch projection undefinable ist, werden mit dem Aufruf die neuen konfliktverursachenden Zellenpaare berechnet
      */
      if(isProjectionDefinable()) {
        break;
      }
    }
  }

  Formula QE::constructImplicant(const carl::tree<smtrat::cad::Sample>::iterator& sample) {
    /* Konstruiere einen. die CAD-Zelle c capturenden Implicant
    * - Bestimme alle atomic formulas, die in c zu 'True' evaluiert werden
    * - Bestimme zu jeder CAD-Zelle c' aus der Menge der falschen CAD-Zellen
    *   die Menge der atomic formulas, die in c' zu 'False' evaluiert werden
    * - Berechne ein Hitting Set der Menge dieser Mengen
    * - Bilde den Implicant als die Konjunktion der Elemente des Hitting Sets
    */

    // Zum Speichern eines Assignments und Models
    Assignment assignment;
    carl::Model<Rational, Polynomial> model;

    // Die Menge der atomic formulas, die in c zu 'True' evaluiert werden
    Formulas L;

    // Das Assignment von c bestimmen (c wird durch 'sample' repraesentiert)
    assignment = mCAD.getLifting().extractSampleMap(sample);

    // Das Assignment in ein Model umwandeln
    for(const auto& a : assignment) {
      model.emplace(a.first, a.second);
    }

    for(const auto& atomicFormula : mAtomicFormulas) {
      // Wahrheitswert der atomic formula in c durch Einsetzen bestimmen
      if(carl::model::evaluate(atomicFormula, model).asBool()) {
        L.push_back(atomicFormula);
      }
    }

    // Das Assignment und das Model resetten
    assignment.clear();
    model.clear();

    // Die Menge der atomic formulas die in einer falschen CAD-Zelle c' zu 'False' evaluiert werden
    Formulas evaluatedToFalse;

    // Die Menge der Mengen der atomic formulas die in einer falschen CAD-Zelle zu 'False' evaluiert wurden
    std::vector<Formulas> S;

    for(const auto& falseSample : mFalseSamples) {
      // Das Assignment von c' bestimmen (c' wird durch falseSample repraesentiert)
      assignment = mCAD.getLifting().extractSampleMap(falseSample);

      // Das Assignment in ein Model umwandeln
      for(const auto& a : assignment) {
        model.emplace(a.first, a.second);
      }

      for(const auto& atomicFormula : L) {
        // Wahrheitswert der atomic formula in c' durch Einsetzen bestimmen
        if(!carl::model::evaluate(atomicFormula, model).asBool()) {
          evaluatedToFalse.push_back(atomicFormula);
        }
      }

      // Das Assignment und das Model resetten
      assignment.clear();
      model.clear();

      // Falls die Menge der zu 'False' evaluierten atomic formulas nicht leer ist
      if(!evaluatedToFalse.empty()) {
        // Fuege die Menge zu S hinzu
        S.push_back(evaluatedToFalse);

        // Resette die Menge der zu 'False' evaluierten atomic formulas
        evaluatedToFalse.clear();
      }
    }

    // Berechne ein Hitting Set der Menge der Mengen
    Formulas H = computeHittingSet(S);

    // Bilde den Implicant als die Konjunktion der Elemente des Hitting Sets
    return Formula(carl::FormulaType::AND, H);
  }

  Formula QE::constructSolutionFormula() {
    /* Konstruiere eine aequivalente, quantorenfreie Formel
    * - Bestimme alle k-Level CAD-Zellen die zu 'wahr' evaluiert werden
    * - Bestimme alle k-Level CAD-Zellen die zu 'falsch' evaluiert werden
    * - Bestimme alle atomic formulas aus den Projektionsfaktoren
    */

    // Bestimme alle k-Level CAD-Zellen die zu 'wahr'/'falsch' evaluiert werden
    for(auto sample_iterator = mCAD.getLifting().getTree().begin_depth(k); sample_iterator != mCAD.getLifting().getTree().end_depth(); sample_iterator++) {
      if(mTruth.find(sample_iterator)->second) {
        mTrueSamples.push_back(sample_iterator);
      }else {
        mFalseSamples.push_back(sample_iterator);
      }
    }

    // Fuer Level 1 bis k
    for(int level = 1; level <= k; level++) {
      // Iteriere ueber alle Projektionsfaktoren des Levels
      std::size_t numberOfProjectionFactors = mCAD.getProjection().size(n + 1 - level);
      for(int id = 0; id < numberOfProjectionFactors; id++) {
        if(mCAD.getProjection().hasPolynomialById(n + 1 - level, id)) {
          // Bestimme den Projektionsfaktor
          Polynomial p = (Polynomial) mCAD.getProjection().getPolynomialById(n + 1 - level, id);

          // Bilde eine atomic formula fuer den Projektionsfaktor und jede sign condition
          mAtomicFormulas.push_back(Formula(Constraint(p, carl::Relation::EQ)));
          mAtomicFormulas.push_back(Formula(Constraint(p, carl::Relation::NEQ)));
          mAtomicFormulas.push_back(Formula(Constraint(p, carl::Relation::LESS)));
          mAtomicFormulas.push_back(Formula(Constraint(p, carl::Relation::LEQ)));
          mAtomicFormulas.push_back(Formula(Constraint(p, carl::Relation::GREATER)));
          mAtomicFormulas.push_back(Formula(Constraint(p, carl::Relation::GEQ)));
        }
      }
    }

    // Die Menge der implicants
    Formulas implicants;

    // Um festzuhalten ob eine CAD-Zelle bereits von einem der implicanten gecapured wurde
    bool captured = false;

    // Fuer jede wahre k-Level CAD-Zelle
    for(auto const& sample : mTrueSamples) {
      // Das Assignment von c bestimmen
      Assignment assignment = mCAD.getLifting().extractSampleMap(sample);

      // Das Assignment in ein Model umwandeln
      carl::Model<Rational, Polynomial> model;
      for(const auto& a : assignment) {
        model.emplace(a.first, a.second);
      }

      // Pruefe ob die CAD-Zelle c (repraesentiert durch 'sample') bereits durch einen der imlicants gecaptured wird
      for(auto const& implicant : implicants) {
        // Falls die CAD-Zelle c durch einen implicant bereits gecaptured wurde, setze captured auf 'True
        if(carl::model::evaluate(implicant, model).asBool()) {
          captured = true;
        }
      }

      // Wenn die CAD-Zelle c (repraesentiert durch 'sample') noch nicht von einem implicant gecaptured wird
      if(!captured) {
        // Konstruiere einen implicant der c captured
        Formula implicant = constructImplicant(sample);
        implicants.push_back(implicant);
      }

      captured = false;
    }

    // Bestimme fuer jede wahre k-Level CAD-Zelle die Menge der implicants die diese capturend

    // Die Menge der impicanten die eine der wahren CAD-Zellen capturen
    Formulas i;
    // Die Menge der Mengen von implicanten die eine der wahren CAD-Zelle capturen
    std::vector<Formulas> I;

    // Fuer jede wahre k-Level CAD-Zelle
    for(auto const& sample : mTrueSamples) {
      // Das Assignment von der CAD-Zelle (repraesentiert durch 'sample') bestimmen
      Assignment assignment = mCAD.getLifting().extractSampleMap(sample);

      // Das Assignment in ein Model umwandeln
      carl::Model<Rational, Polynomial> model;
      for(const auto& a : assignment) {
        model.emplace(a.first, a.second);
      }

      // Pruefe welche implicants die CAD-Zelle capturen
      for(auto const& implicant : implicants) {
        // Falls die CAD-Zelle durch einen implicant gecaptured wurde, fuege ihn der Menge i hinzu
        if(carl::model::evaluate(implicant, model).asBool()) {
          i.push_back(implicant);
        }
      }

      // Falls die Menge der implicanten nicht leer ist
      if(!i.empty()) {
        // Die Menge der implicanten I hinzufuegen
        I.push_back(i);

        // Die Menge der implicanten resetten
        i.clear();
      }
    }

    // Ein Hitting Set der Menge der Mengen von implicanten berechnen
    Formulas H = computeHittingSet(I);

    // Bilde die aequivalente, quantorenfreie Formel als Disjunktion der Elemente des Hitting Sets
    return Formula(carl::FormulaType::OR, H);
  }

  Formula QE::constructSolutionFormula_OriginalMethod() {
    /* Konstruiere eine aequivalente, quantorenfreie Forme, nach der Beschreibung in Col75
    * - Bestimme alle k-Level CAD-Zellen die zu 'wahr' evaluiert werden
    * - Bestimme die projection-based formula
    */

    // Bestimme alle k-Level CAD-Zellen die zu 'wahr' evaluiert werden
    for(auto sample_iterator = mCAD.getLifting().getTree().begin_depth(k); sample_iterator != mCAD.getLifting().getTree().end_depth(); sample_iterator++) {
      if(mTruth.find(sample_iterator)->second) {
        mTrueSamples.push_back(sample_iterator);
      }
    }


    // Bestimme die projection-based formula
    Formulas disjunction;

    for(auto const& sample : mTrueSamples) {
      Formulas conjunction;

      // Fuer Level 1 bis k
      for(int level = 1; level <= k; level++) {
        // Iteriere ueber alle Projektionsfaktoren des Levels
        std::size_t numberOfProjectionFactors = mCAD.getProjection().size(n + 1 - level);
        for(int id = 0; id < numberOfProjectionFactors; id++) {
          if(mCAD.getProjection().hasPolynomialById(n + 1 - level, id)) {
            // Bestimme den Projektionsfaktor
            Polynomial p = (Polynomial) mCAD.getProjection().getPolynomialById(n + 1 - level, id);

            // Bestimme das Sign des Projektionsfaktors in der durch sample repraesentierten CAD-Zelle
            carl::Sign sign = carl::sgn(carl::RealAlgebraicNumberEvaluation::evaluate((Polynomial) p, mCAD.getLifting().extractSampleMap(sample)));

            // Bilde eine atomic formula fuer den Projektionsfaktor und das Sign
            switch(sign) {
              case carl::Sign::NEGATIVE: conjunction.push_back(Formula(Constraint(p, carl::Relation::LESS))); break;
              case carl::Sign::ZERO: conjunction.push_back(Formula(Constraint(p, carl::Relation::EQ))); break;
              case carl::Sign::POSITIVE: conjunction.push_back(Formula(Constraint(p, carl::Relation::GREATER))); break;
            }
          }
        }
      }

      disjunction.push_back(Formula(carl::FormulaType::AND, conjunction));
    }

    return Formula(carl::FormulaType::OR, disjunction);
  }

  template<typename T>
  std::vector<T> QE::computeHittingSet(const std::vector<std::vector<T>>& setOfSets) {
    /* Berechne ein Hitting Set der uebergebenen Menge von Mengen
    * - Mithilfe eines klassischen Greedy Ansatzes:
    * - Fuege stets das Element, dass die meisten mengen hittet dem Hitting Set hinzu
    * - Solange bis alle Mengen mindestens einmal gehittet wurden
    */

    // Sicherheitsmassnahme: Um die uebergebenen Daten nicht zu manipulieren, kopieren wir die uebergebene Menge von Mengen
    std::vector<std::vector<T>> SoS;
    for(auto set = setOfSets.begin(); set != setOfSets.end(); set++) {
      SoS.push_back(*set);
    }

    // Das HittingSet
    std::vector<T> H;
    // Das Universum, aller Elemente aus allen Mengen aus der Menge von Mengen
    std::map<T, int> U;

    // Baue das Universum auf
    for(auto set = SoS.begin(); set != SoS.end(); set++) {
      for(auto element = set->begin(); element != set->end(); element++) {
        if(U.find(*element) != U.end()) {
          U.find(*element)->second++;
        }else {
          U.emplace(*element,1);
        }
      }
    }

    // Solange bis alle Mengen mindestens einmal gehittet wurden
    while(!SoS.empty()) {
      // Das Element finden, dass die meisten Mengen hittet
      auto max = U.begin();
      for(auto it = U.begin(); it != U.end(); it++) {
        // Das Element hittet mehr Elemente
        if(it->second > max->second) {
          max = it;
        }
      }

      // Das Element, dass die meisten Mengen hittet dem Hitting Set hinzufuegen
      H.push_back(max->first);

      // Alle gehitteten Mengen aus der Menge von Mengen entfernen
      for(auto set = SoS.begin(); set != SoS.end();) {
        // Das Element ist in der Menge, die Menge kann also entfernt werden
        if(std::find(set->begin(), set->end(), max->first) != set->end()) {
          set = SoS.erase(set);
        }else {
          set++;
        }
      }

      // Loesche das Element dass die meisten Mengen gehittet hat aus dem Universum
      U.erase(max);

      // Falls das Universum jetzt nicht leer sein sollte, baue es neu auf
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

  void QE::printProjectionFactorsPerLevel(std::size_t level) {
    /* Anmerkung:
    * - Die Level der Projektionsfaktoren werden anders als die der CAD-Zellen gezaehlt
    */

    std::cout << "------------------------------------------------------------------------" << std::endl;
    std::cout << "Ausgabe aller Projektionsfaktoren des Level " << level << "." << std::endl;
    std::cout << std::endl;

    // Level "korrigieren"
    level = n + 1 - level;

    // AUSGABE: alle Projektionsfaktoren des Levels
    std::size_t numberOfProjectionFactors = mCAD.getProjection().size(level);
    for(int id = 0; id < numberOfProjectionFactors; id++) {
      if(mCAD.getProjection().hasPolynomialById(level, id)) {
        std::cout << mCAD.getProjection().getPolynomialById(level, id) << std::endl;
      }
    }
    std::cout << std::endl;
  }

  void QE::printCADCellsPerLevel(std::size_t level) {
    std::cout << "------------------------------------------------------------------------" << std::endl;
    std::cout << "Ausgabe aller CAD-Zellen des Level " << level << "." << std::endl;
    std::cout << std::endl;

    // AUSGABE: alle CAD-Zellen des Levels
    for(auto it = mCAD.getLifting().getTree().begin_depth(level); it != mCAD.getLifting().getTree().end_depth(); it++) {
      std::cout << mCAD.getLifting().extractSampleMap(it) << std::endl;
    }
    std::cout << std::endl;
  }

} // End of namespace qe
} // End of namespace smtrat
