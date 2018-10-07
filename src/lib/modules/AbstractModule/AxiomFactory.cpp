/**
 * Class to create the formulas for axioms.
 * @author Aklima Zaman
 * @since 2018-09-24
 * @version 2018-09-24
 */

#include "AxiomFactory.h"

namespace smtrat {

    FormulaT createZeroOne(carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable) {
        FormulaT xFormula = FormulaT(Poly(xVariable), carl::Relation::EQ);
        FormulaT yFormula = FormulaT(Poly(yVariable), carl::Relation::EQ);
        FormulaT zFormula = FormulaT(Poly(zVariable), carl::Relation::EQ);

        FormulaT leftFormula = FormulaT(carl::FormulaType::OR, xFormula, yFormula);

        FormulaT finalFormula = FormulaT(carl::FormulaType::IFF, leftFormula, zFormula);

        cout << "\n";
        cout << "created ZeroOne Axiom Formula is: " << finalFormula;
        cout << "\n";

        return finalFormula;

    }

    FormulaT createZeroTwo(carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable) {

        FormulaT xFormulaGrater = FormulaT(Poly(xVariable), carl::Relation::GREATER);
        FormulaT yFormulaGrater = FormulaT(Poly(yVariable), carl::Relation::GREATER);
        FormulaT partOneFormula = FormulaT(carl::FormulaType::AND, xFormulaGrater, yFormulaGrater);

        FormulaT xFormulaLess = FormulaT(Poly(xVariable), carl::Relation::LESS);
        FormulaT yFormulaLess = FormulaT(Poly(yVariable), carl::Relation::LESS);
        FormulaT partTwoFormula = FormulaT(carl::FormulaType::AND, xFormulaLess, yFormulaLess);

        FormulaT zFormula = FormulaT(Poly(zVariable), carl::Relation::GREATER);

        FormulaT leftFormula = FormulaT(carl::FormulaType::OR, partOneFormula, partTwoFormula);

        FormulaT finalFormula = FormulaT(carl::FormulaType::IFF, leftFormula, zFormula);

        cout << "\n";
        cout << "created ZeroTwo Axiom Formula is: " << finalFormula;
        cout << "\n";

        return finalFormula;

    }

    FormulaT createZeroThree(carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable) {

        FormulaT xFormulaGrater = FormulaT(Poly(xVariable), carl::Relation::LESS);
        FormulaT yFormulaGrater = FormulaT(Poly(yVariable), carl::Relation::GREATER);
        FormulaT partOneFormula = FormulaT(carl::FormulaType::AND, xFormulaGrater, yFormulaGrater);

        FormulaT xFormulaLess = FormulaT(Poly(xVariable), carl::Relation::GREATER);
        FormulaT yFormulaLess = FormulaT(Poly(yVariable), carl::Relation::LESS);
        FormulaT partTwoFormula = FormulaT(carl::FormulaType::AND, xFormulaLess, yFormulaLess);

        FormulaT zFormula = FormulaT(Poly(zVariable), carl::Relation::LESS);

        FormulaT leftFormula = FormulaT(carl::FormulaType::OR, partOneFormula, partTwoFormula);

        FormulaT finalFormula = FormulaT(carl::FormulaType::IFF, leftFormula, zFormula);

        cout << "\n";
        cout << "created ZeroThree Axiom Formula is: " << finalFormula;
        cout << "\n";

        return finalFormula;

    }

    FormulasT AxiomFactory::createFormula(AxiomType axiomType, MonomialMap monomialMap) {

        FormulasT formulas;

        for (MonomialMapIterator monomialIterator = monomialMap.begin(); monomialIterator != monomialMap.end(); ++monomialIterator){
            carl::Variable zVariable = monomialIterator->first;

            carl::Monomial::Arg monomial = monomialIterator->second;

            auto it = monomial->begin();
            carl::Variable xVariable = it->first;
            carl::Variable yVariable = it->first;
            ++it;
            if (it != monomial->end()){
                yVariable = it->first;
            }

            cout << "\n";
            cout << "zVariable is: " << zVariable;
            cout << "\n";
            cout << "xVariable is: " << xVariable;
            cout << "\n";
            cout << "yVariable is: " << yVariable;
            cout << "\n";

            if (axiomType == AxiomType::ZERO) {
                formulas.push_back(createZeroOne(xVariable, yVariable, zVariable));
                formulas.push_back(createZeroTwo(xVariable, yVariable, zVariable));
                formulas.push_back(createZeroThree(xVariable, yVariable, zVariable));
            } else if (axiomType == AxiomType::TANGENT_PLANE){

            }
        }

        return formulas;
    }


}

