/**
 * Class to create the formulas for axioms.
 * @author Aklima Zaman
 * @since 2018-09-24
 * @version 2018-09-24
 */

#include "AxiomFactory.h"

namespace smtrat {

    FormulaT createZeroOne(carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable) {
        // x = 0
        FormulaT xFormula = FormulaT(Poly(xVariable), carl::Relation::EQ);
        // y = 0
        FormulaT yFormula = FormulaT(Poly(yVariable), carl::Relation::EQ);
        // z = 0
        FormulaT zFormula = FormulaT(Poly(zVariable), carl::Relation::EQ);

        // x = 0 | y = 0
        FormulaT leftFormula = FormulaT(carl::FormulaType::OR, xFormula, yFormula);

        // (x = 0 | y = 0) <-> (z = 0)
        FormulaT finalFormula = FormulaT(carl::FormulaType::IFF, leftFormula, zFormula);

        cout << "\n";
        cout << "created ZeroOne Axiom Formula is: " << finalFormula;
        cout << "\n";


        return finalFormula;

    }

    FormulaT createZeroTwo(carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable) {

        // x > 0
        FormulaT xFormulaGrater = FormulaT(Poly(xVariable), carl::Relation::GREATER);
        // y > 0
        FormulaT yFormulaGrater = FormulaT(Poly(yVariable), carl::Relation::GREATER);
        // x > 0 && y > 0
        FormulaT partOneFormula = FormulaT(carl::FormulaType::AND, xFormulaGrater, yFormulaGrater);

        // x < 0
        FormulaT xFormulaLess = FormulaT(Poly(xVariable), carl::Relation::LESS);
        // y < 0
        FormulaT yFormulaLess = FormulaT(Poly(yVariable), carl::Relation::LESS);
        // x < 0 && y < 0
        FormulaT partTwoFormula = FormulaT(carl::FormulaType::AND, xFormulaLess, yFormulaLess);

        // z > 0
        FormulaT zFormula = FormulaT(Poly(zVariable), carl::Relation::GREATER);

        // (x > 0 && y > 0) | (x < 0 && y < 0)
        FormulaT leftFormula = FormulaT(carl::FormulaType::OR, partOneFormula, partTwoFormula);

        // (x > 0 && y > 0) | (x < 0 && y < 0) <-> z > 0
        FormulaT finalFormula = FormulaT(carl::FormulaType::IFF, leftFormula, zFormula);

        cout << "\n";
        cout << "created ZeroTwo Axiom Formula is: " << finalFormula;
        cout << "\n";

        return finalFormula;

    }

    FormulaT createZeroThree(carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable) {

        // x < 0
        FormulaT xFormulaGrater = FormulaT(Poly(xVariable), carl::Relation::LESS);
        // y > 0
        FormulaT yFormulaGrater = FormulaT(Poly(yVariable), carl::Relation::GREATER);
        // x < 0 && y > 0
        FormulaT partOneFormula = FormulaT(carl::FormulaType::AND, xFormulaGrater, yFormulaGrater);

        // x > 0
        FormulaT xFormulaLess = FormulaT(Poly(xVariable), carl::Relation::GREATER);
        // y < 0
        FormulaT yFormulaLess = FormulaT(Poly(yVariable), carl::Relation::LESS);
        // x > 0 && y < 0
        FormulaT partTwoFormula = FormulaT(carl::FormulaType::AND, xFormulaLess, yFormulaLess);

        // z < 0
        FormulaT zFormula = FormulaT(Poly(zVariable), carl::Relation::LESS);

        // (x < 0 && y > 0) | (x > 0 && y < 0)
        FormulaT leftFormula = FormulaT(carl::FormulaType::OR, partOneFormula, partTwoFormula);

        // (x < 0 && y > 0) | (x > 0 && y < 0) <-> z < 0
        FormulaT finalFormula = FormulaT(carl::FormulaType::IFF, leftFormula, zFormula);

        cout << "\n";
        cout << "created ZeroThree Axiom Formula is: " << finalFormula;
        cout << "\n";

        return finalFormula;

    }

    FormulaT createTangentPlaneNEQOne (carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable, carl::Variable aVariable) {

        // {x, a}
        std::vector<Poly> operands {Poly(xVariable), Poly(aVariable)};

        // x - a = 0
        FormulaT leftFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands), carl::Relation::EQ);

        // {z, a*y}
        std::vector<Poly> operands2 {Poly(zVariable), Poly(aVariable*yVariable)};

        // z - a*y = 0
        FormulaT zFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands2), carl::Relation::EQ);

        // (x - a = 0) -> (z - a*y = 0)
        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, zFormula);

        cout << "\n";
        cout << "created TangentPlaneNEQOne Axiom Formula is: " << finalFormula;
        cout << "\n";

        return finalFormula;

    }

    FormulaT createTangentPlaneNEQTwo (carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable, carl::Variable bVariable) {

        // {y, b}
        std::vector<Poly> operands {Poly(yVariable), Poly(bVariable)};
        // y - b = 0
        FormulaT leftFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands), carl::Relation::EQ);

        // {z, b*x}
        std::vector<Poly> operands2 {Poly(zVariable), Poly(bVariable*xVariable)};
        // z - b*x = 0
        FormulaT zFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands2), carl::Relation::EQ);

        // (y - b = 0) -> (z - b*x = 0)
        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, zFormula);

        cout << "\n";
        cout << "created TangentPlaneNEQTwo Axiom Formula is: " << finalFormula;
        cout << "\n";

        return finalFormula;

    }

    FormulaT createTangentPlaneNEQThree (carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable, carl::Variable aVariable, carl::Variable bVariable) {

        // {x, a}
        std::vector<Poly> operandsxa {Poly(xVariable), Poly(aVariable)};
        // Poly(x - a)
        Poly xMinusa = Poly(Poly::ConstructorOperation::SUB, operandsxa);

        // {y, b}
        std::vector<Poly> operandsyb {Poly(yVariable), Poly(bVariable)};
        // Poly(y - b)
        Poly yMinusb =Poly(Poly::ConstructorOperation::SUB, operandsyb);

        FormulaT formula1 = FormulaT(xMinusa, carl::Relation::GREATER);
        FormulaT formula2 = FormulaT(yMinusb, carl::Relation::LESS);
        FormulaT partOneFormula = FormulaT(carl::FormulaType::AND, formula1, formula2);


        FormulaT formula3 = FormulaT(xMinusa, carl::Relation::LESS);
        FormulaT formula4 = FormulaT(yMinusb, carl::Relation::GREATER);
        FormulaT partTwoFormula = FormulaT(carl::FormulaType::AND, formula3, formula4);

        FormulaT leftFormula = FormulaT(carl::FormulaType::OR, partOneFormula, partTwoFormula);

        // {z, -b*x, -a*y, a*b}
        std::vector<Poly> operandsz {Poly(zVariable), -Poly(bVariable*xVariable), -Poly(aVariable*yVariable), Poly(aVariable*bVariable)};
        // z - b*x - a*y + a*b = 0
        Poly zLeftPoly = Poly(Poly::ConstructorOperation::ADD, operandsz);
        FormulaT zFormula = FormulaT(zLeftPoly, carl::Relation::LESS);

        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, zFormula);

        cout << "\n";
        cout << "created TangentPlaneNEQThree Axiom Formula is: " << finalFormula;
        cout << "\n";


        return finalFormula;

    }

    FormulaT createTangentPlaneNEQFour (carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable, carl::Variable aVariable, carl::Variable bVariable) {

        // {x, a}
        std::vector<Poly> operandsxa {Poly(xVariable), Poly(aVariable)};
        // Poly(x - a)
        Poly xMinusa = Poly(Poly::ConstructorOperation::SUB, operandsxa);

        // {y, b}
        std::vector<Poly> operandsyb {Poly(yVariable), Poly(bVariable)};
        // Poly(y - b)
        Poly yMinusb =Poly(Poly::ConstructorOperation::SUB, operandsyb);

        FormulaT formula1 = FormulaT(xMinusa, carl::Relation::LESS);
        FormulaT formula2 = FormulaT(yMinusb, carl::Relation::LESS);
        FormulaT partOneFormula = FormulaT(carl::FormulaType::AND, formula1, formula2);


        FormulaT formula3 = FormulaT(xMinusa, carl::Relation::GREATER);
        FormulaT formula4 = FormulaT(yMinusb, carl::Relation::GREATER);
        FormulaT partTwoFormula = FormulaT(carl::FormulaType::AND, formula3, formula4);

        FormulaT leftFormula = FormulaT(carl::FormulaType::OR, partOneFormula, partTwoFormula);

        // {z, -b*x, -a*y, a*b}
        std::vector<Poly> operandsz {Poly(zVariable), -Poly(bVariable*xVariable), -Poly(aVariable*yVariable), Poly(aVariable*bVariable)};
        // z - b*x - a*y + a*b = 0
        Poly zLeftPoly = Poly(Poly::ConstructorOperation::ADD, operandsz);
        FormulaT zFormula = FormulaT(zLeftPoly, carl::Relation::GREATER);

        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, zFormula);

        cout << "\n";
        cout << "created TangentPlaneNEQFour Axiom Formula is: " << finalFormula;
        cout << "\n";


        return finalFormula;

    }

    FormulaT createTangentPlaneEQOne (carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable, carl::Variable aVariable) {

        std::vector<Poly> operands {Poly(xVariable), Poly(aVariable)};
        FormulaT leftFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands), carl::Relation::EQ);

        std::vector<Poly> operands2 {Poly(zVariable), Poly(aVariable*yVariable)};
        FormulaT zFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands2), carl::Relation::EQ);

        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, zFormula);

        cout << "\n";
        cout << "created TangentPlaneEQOne Axiom Formula is: " << finalFormula;
        cout << "\n";

        return finalFormula;

    }

    FormulaT createTangentPlaneEQTwo (carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable, carl::Variable aVariable) {

        std::vector<Poly> operands {Poly(xVariable), Poly(aVariable)};
        FormulaT leftFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands), carl::Relation::NEQ);

        std::vector<Poly> operands2 {Poly(zVariable), Poly(aVariable*xVariable), Poly(aVariable*xVariable), Poly(aVariable*aVariable)};
        FormulaT zFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands2), carl::Relation::EQ);

        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, zFormula);

        cout << "\n";
        cout << "created TangentPlaneEQTwo Axiom Formula is: " << finalFormula;
        cout << "\n";

        return finalFormula;

    }

    const smtrat::VariableCapsule extractVariables(MonomialMapIterator monomialIterator) {
        carl::Variable zVariable = monomialIterator->first;
        carl::Monomial::Arg monomial = monomialIterator->second;

        auto it = monomial->begin();

        carl::Variable xVariable = it->first;
        carl::Variable yVariable = it->first;

        ++it;
        // if the second variable is not the same, e.g. x * y
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

        smtrat::VariableCapsule capsule(xVariable, yVariable, zVariable);
        return capsule;

    }

    FormulaT createMonotonicityOne(smtrat::VariableCapsule variableCapsule, smtrat::VariableCapsule variableCapsuleInner){
        // {x_1, x_2}
        std::vector<Poly> operandsxx {Poly(variableCapsule.getXVariable()), Poly(variableCapsuleInner.getXVariable())};
        // x_1 - x_2 <= 0
        FormulaT partOneLeftFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operandsxx), carl::Relation::LEQ);

        // {y_1, y_2}
        std::vector<Poly> operandsyy {Poly(variableCapsule.getYVariable()), Poly(variableCapsuleInner.getYVariable())};
        // y_1 - y_2 <= 0
        FormulaT partTwoLeftFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operandsyy), carl::Relation::LEQ);

        // (x_1 - x_2 <= 0) && (y_1 - y_2 <= 0)
        FormulaT leftFormula = FormulaT(carl::FormulaType::AND, partOneLeftFormula, partTwoLeftFormula);

        // {z_1, z_2}
        std::vector<Poly> operandszz {Poly(variableCapsule.getZVariable()), Poly(variableCapsuleInner.getZVariable())};
        // z_1 - z_2 <= 0
        FormulaT zFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operandszz), carl::Relation::LEQ);

        // (x_1 - x_2 <= 0) && (y_1 - y_2 <= 0) -> (z_1 - z_2 <= 0)
        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, zFormula);

        cout << "\n";
        cout << "created MonotonicityOne Axiom Formula is: " << finalFormula;
        cout << "\n";

        return finalFormula;
    }

    FormulaT createMonotonicityTwo(smtrat::VariableCapsule variableCapsule, smtrat::VariableCapsule variableCapsuleInner){
        // {x_1, x_2}
        std::vector<Poly> operandsxx {Poly(variableCapsule.getXVariable()), Poly(variableCapsuleInner.getXVariable())};
        // x_1 - x_2 < 0
        FormulaT partOneLeftFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operandsxx), carl::Relation::LESS);

        // {y_1, y_2}
        std::vector<Poly> operandsyy {Poly(variableCapsule.getYVariable()), Poly(variableCapsuleInner.getYVariable())};
        // y_1 - y_2 <= 0
        FormulaT partTwoLeftFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operandsyy), carl::Relation::LEQ);

        // y_2 != 0
        FormulaT partThreeLeftFormula = FormulaT(Poly(variableCapsuleInner.getYVariable()), carl::Relation::NEQ);

        // (x_1 - x_2 < 0) && (y_1 - y_2 <= 0) && (y_2 != 0)
        FormulaT leftFormula = FormulaT(carl::FormulaType::AND, partOneLeftFormula, partTwoLeftFormula, partThreeLeftFormula);

        // {z_1, z_2}
        std::vector<Poly> operandszz {Poly(variableCapsule.getZVariable()), Poly(variableCapsuleInner.getZVariable())};
        // z_1 - z_2 < 0
        FormulaT zFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operandszz), carl::Relation::LESS);

        // (x_1 - x_2 < 0) && (y_1 - y_2 <= 0) && (y_2 != 0) -> (z_1 - z_2 < 0)
        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, zFormula);

        cout << "\n";
        cout << "created MonotonicityTwo Axiom Formula is: " << finalFormula;
        cout << "\n";

        return finalFormula;
    }

    FormulaT createMonotonicityThree(smtrat::VariableCapsule variableCapsule, smtrat::VariableCapsule variableCapsuleInner){
        // {x_1, x_2}
        std::vector<Poly> operandsxx {Poly(variableCapsule.getXVariable()), Poly(variableCapsuleInner.getXVariable())};
        // x_1 - x_2 <= 0
        FormulaT partOneLeftFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operandsxx), carl::Relation::LEQ);

        // {y_1, y_2}
        std::vector<Poly> operandsyy {Poly(variableCapsule.getYVariable()), Poly(variableCapsuleInner.getYVariable())};
        // y_1 - y_2 < 0
        FormulaT partTwoLeftFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operandsyy), carl::Relation::LESS);

        // x_2 != 0
        FormulaT partThreeLeftFormula = FormulaT(Poly(variableCapsuleInner.getXVariable()), carl::Relation::NEQ);

        // (x_1 - x_2 <= 0) && (y_1 - y_2 < 0) && (x_2 != 0)
        FormulaT leftFormula = FormulaT(carl::FormulaType::AND, partOneLeftFormula, partTwoLeftFormula, partThreeLeftFormula);

        // {z_1, z_2}
        std::vector<Poly> operandszz {Poly(variableCapsule.getZVariable()), Poly(variableCapsuleInner.getZVariable())};
        // z_1 - z_2 < 0
        FormulaT zFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operandszz), carl::Relation::LESS);

        // (x_1 - x_2 <= 0) && (y_1 - y_2 < 0) && (x_2 != 0) -> (z_1 - z_2 < 0)
        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, zFormula);

        cout << "\n";
        cout << "created MonotonicityThree Axiom Formula is: " << finalFormula;
        cout << "\n";

        return finalFormula;
    }

    FormulaT createCongruence(smtrat::VariableCapsule variableCapsuleOuter, smtrat::VariableCapsule variableCapsuleInner){
        // {x_1, x_2}
        std::vector<Poly> operandsxx {Poly(variableCapsuleOuter.getXVariable()), Poly(variableCapsuleInner.getXVariable())};
        // x_1 - x_2 = 0
        FormulaT partOneLeftFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operandsxx), carl::Relation::EQ);

        // {y_1, y_2}
        std::vector<Poly> operandsyy {Poly(variableCapsuleOuter.getYVariable()), Poly(variableCapsuleInner.getYVariable())};
        // y_1 - y_2 = 0
        FormulaT partTwoLeftFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operandsyy), carl::Relation::EQ);

        // (x_1 - x_2 = 0) && (y_1 - y_2 = 0)
        FormulaT leftFormula = FormulaT(carl::FormulaType::AND, partOneLeftFormula, partTwoLeftFormula);

        // {z_1, z_2}
        std::vector<Poly> operandszz {Poly(variableCapsuleOuter.getZVariable()), Poly(variableCapsuleInner.getZVariable())};
        // z_1 - z_2 = 0
        FormulaT zFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operandszz), carl::Relation::EQ);

        // (x_1 - x_2 = 0) && (y_1 - y_2 = 0) -> (z_1 - z_2 = 0)
        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, zFormula);

        cout << "\n";
        cout << "created Congruence Axiom Formula is: " << finalFormula;
        cout << "\n";

        return finalFormula;
    }


    FormulasT AxiomFactory::createFormula(AxiomType axiomType, MonomialMap monomialMap) {

        FormulasT formulas;

        for (MonomialMapIterator monomialIteratorOuter = monomialMap.begin(); monomialIteratorOuter != monomialMap.end(); ++monomialIteratorOuter){

            smtrat::VariableCapsule variableCapsuleOuter = extractVariables(monomialIteratorOuter);

            carl::Variable xVariable = variableCapsuleOuter.getXVariable();
            carl::Variable yVariable = variableCapsuleOuter.getYVariable();
            carl::Variable zVariable = variableCapsuleOuter.getZVariable();

            carl::Variable aVariable = carl::freshRealVariable("a");
            carl::Variable bVariable = carl::freshRealVariable("b");

            if (axiomType == AxiomType::ZERO) {
                formulas.push_back(createZeroOne(xVariable, yVariable, zVariable));
                formulas.push_back(createZeroTwo(xVariable, yVariable, zVariable));
                formulas.push_back(createZeroThree(xVariable, yVariable, zVariable));
            } else if (axiomType == AxiomType::TANGENT_PLANE){
                if (xVariable != yVariable){
                    formulas.push_back(createTangentPlaneNEQOne(xVariable, yVariable, zVariable, aVariable));
                    formulas.push_back(createTangentPlaneNEQTwo(xVariable, yVariable, zVariable, bVariable));
                    formulas.push_back(createTangentPlaneNEQThree(xVariable, yVariable, zVariable, aVariable, bVariable));
                    formulas.push_back(createTangentPlaneNEQFour(xVariable, yVariable, zVariable, aVariable, bVariable));
                } else {
                    formulas.push_back(createTangentPlaneEQOne(xVariable, yVariable, zVariable, aVariable));
                    formulas.push_back(createTangentPlaneEQTwo(xVariable, yVariable, zVariable, aVariable));
                }
            } else if(axiomType == AxiomType::MONOTONICITY || axiomType == AxiomType::CONGRUENCE){
                    bool flag = false;
                    for (MonomialMapIterator monomialIteratorInner = monomialMap.begin(); monomialIteratorInner != monomialMap.end(); ++monomialIteratorInner){
                        if (monomialIteratorOuter == monomialIteratorInner){
                            flag = true;
                        }
                        if (flag && monomialIteratorOuter != monomialIteratorInner){
                            smtrat::VariableCapsule variableCapsuleInner = extractVariables(monomialIteratorInner);
                            if (axiomType == AxiomType::MONOTONICITY){
                                formulas.push_back(createMonotonicityOne(variableCapsuleOuter, variableCapsuleInner));
                                formulas.push_back(createMonotonicityTwo(variableCapsuleOuter, variableCapsuleInner));
                                formulas.push_back(createMonotonicityThree(variableCapsuleOuter, variableCapsuleInner));
                            } else if (axiomType == AxiomType::CONGRUENCE){
                                formulas.push_back(createCongruence(variableCapsuleOuter, variableCapsuleInner));
                            }

                        }
                    }

            }
        }



        return formulas;
    }


}

