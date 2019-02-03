/**
 * Class to create the formulas for axioms.
 * @author Aklima Zaman
 * @since 2018-09-24
 * @version 2018-09-24
 */

#include "AxiomFactory.h"
#include "../LOG.h"

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

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "\n";
            cout << "created ZeroOne Axiom Formula is: " << finalFormula;
            cout << "\n";
        }

        return finalFormula;

    }

    FormulaT createZeroTwo(carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable) {

        // x > 0
        FormulaT xFormulaGreater = FormulaT(Poly(xVariable), carl::Relation::GREATER);
        // y > 0
        FormulaT yFormulaGreater = FormulaT(Poly(yVariable), carl::Relation::GREATER);
        // x > 0 && y > 0
        FormulaT partOneFormula = FormulaT(carl::FormulaType::AND, xFormulaGreater, yFormulaGreater);

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

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "\n";
            cout << "created ZeroTwo Axiom Formula is: " << finalFormula;
            cout << "\n";
        }

        return finalFormula;

    }

    FormulaT createZeroThree(carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable) {

        // x < 0
        FormulaT xFormulaLess = FormulaT(Poly(xVariable), carl::Relation::LESS);
        // y > 0
        FormulaT yFormulaGreater = FormulaT(Poly(yVariable), carl::Relation::GREATER);
        // x < 0 && y > 0
        FormulaT partOneFormula = FormulaT(carl::FormulaType::AND, xFormulaLess, yFormulaGreater);

        // x > 0
        FormulaT xFormulaGreater = FormulaT(Poly(xVariable), carl::Relation::GREATER);
        // y < 0
        FormulaT yFormulaLess = FormulaT(Poly(yVariable), carl::Relation::LESS);
        // x > 0 && y < 0
        FormulaT partTwoFormula = FormulaT(carl::FormulaType::AND, xFormulaGreater, yFormulaLess);

        // z < 0
        FormulaT zFormula = FormulaT(Poly(zVariable), carl::Relation::LESS);

        // (x < 0 && y > 0) | (x > 0 && y < 0)
        FormulaT leftFormula = FormulaT(carl::FormulaType::OR, partOneFormula, partTwoFormula);

        // (x < 0 && y > 0) | (x > 0 && y < 0) <-> z < 0
        FormulaT finalFormula = FormulaT(carl::FormulaType::IFF, leftFormula, zFormula);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "\n";
            cout << "created ZeroThree Axiom Formula is: " << finalFormula;
            cout << "\n";
        }

        return finalFormula;

    }

    FormulaT createTangentPlaneNEQOne (carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable, Rational aRational) {

        // x - a = 0
        FormulaT leftFormula = FormulaT(Poly(xVariable) - aRational, carl::Relation::EQ);

        // z - a*y = 0
        FormulaT rightFormula = FormulaT(Poly(zVariable) - Poly(aRational*yVariable), carl::Relation::EQ);

        // (x - a = 0) -> (z - a*y = 0)
        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, rightFormula);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "\n";
            cout << "created TangentPlaneNEQOne Axiom Formula is: " << finalFormula;
            cout << "\n";
        }

        return finalFormula;

    }

    FormulaT createTangentPlaneNEQTwo (carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable, Rational bRational) {

        // y - b = 0
        FormulaT leftFormula = FormulaT(Poly(yVariable) - bRational, carl::Relation::EQ);

        // z - b*x = 0
        FormulaT rightFormula = FormulaT(Poly(zVariable) - Poly(bRational*xVariable), carl::Relation::EQ);

        // (y - b = 0) -> (z - b*x = 0)
        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, rightFormula);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "\n";
            cout << "created TangentPlaneNEQTwo Axiom Formula is: " << finalFormula;
            cout << "\n";
        }

        return finalFormula;

    }

    FormulaT createTangentPlaneNEQThree (carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable, Rational aRational, Rational bRational) {

        // {x, a}
        std::vector<Poly> operandsxa {Poly(xVariable), Poly(aRational)};
        // Poly(x - a)
        Poly xMinusa = Poly(Poly::ConstructorOperation::SUB, operandsxa);

        // {y, b}
        std::vector<Poly> operandsyb {Poly(yVariable), Poly(bRational)};
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
        std::vector<Poly> operandsz {Poly(zVariable), -Poly(bRational*xVariable), -Poly(aRational*yVariable), Poly(aRational*bRational)};
        // z - b*x - a*y + a*b < 0
        Poly zLeftPoly = Poly(Poly::ConstructorOperation::ADD, operandsz);
        FormulaT rightFormula = FormulaT(zLeftPoly, carl::Relation::LESS);

        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, rightFormula);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "\n";
            cout << "created TangentPlaneNEQThree Axiom Formula is: " << finalFormula;
            cout << "\n";
        }

        return finalFormula;

    }

    FormulaT createTangentPlaneNEQFour (carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable, Rational aRational, Rational bRational) {

        // {x, a}
        std::vector<Poly> operandsxa {Poly(xVariable), Poly(aRational)};
        // Poly(x - a)
        Poly xMinusa = Poly(Poly::ConstructorOperation::SUB, operandsxa);

        // {y, b}
        std::vector<Poly> operandsyb {Poly(yVariable), Poly(bRational)};
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
        std::vector<Poly> operandsz {Poly(zVariable), -Poly(bRational*xVariable), -Poly(aRational*yVariable), Poly(aRational*bRational)};
        // z - b*x - a*y + a*b > 0
        Poly zLeftPoly = Poly(Poly::ConstructorOperation::ADD, operandsz);
        FormulaT rightFormula = FormulaT(zLeftPoly, carl::Relation::GREATER);

        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, rightFormula);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "\n";
            cout << "created TangentPlaneNEQFour Axiom Formula is: " << finalFormula;
            cout << "\n";
        }


        return finalFormula;

    }

    FormulaT createTangentPlaneEQOne (carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable, Rational aRational) {

        std::vector<Poly> operands {Poly(xVariable), Poly(aRational)};
        FormulaT leftFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands), carl::Relation::EQ);

        std::vector<Poly> operands2 {Poly(zVariable), Poly(aRational*yVariable)};
        FormulaT rightFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands2), carl::Relation::EQ);

        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, rightFormula);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "\n";
            cout << "created TangentPlaneEQOne Axiom Formula is: " << finalFormula;
            cout << "\n";
        }

        return finalFormula;

    }

    FormulaT createTangentPlaneEQTwo (carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable, Rational aRational) {

        std::vector<Poly> operands {Poly(xVariable), Poly(aRational)};
        FormulaT leftFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands), carl::Relation::NEQ);

        std::vector<Poly> operands2 {Poly(zVariable), -Poly(aRational*xVariable), -Poly(aRational*xVariable), Poly(aRational*aRational)};
        FormulaT rightFormula = FormulaT(Poly(Poly::ConstructorOperation::ADD, operands2), carl::Relation::GREATER);

        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, rightFormula);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "\n";
            cout << "created TangentPlaneEQTwo Axiom Formula is: " << finalFormula;
            cout << "\n";
        }

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

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "\n";
            cout << "zVariable is: " << zVariable;
            cout << "\n";
            cout << "xVariable is: " << xVariable;
            cout << "\n";
            cout << "yVariable is: " << yVariable;
            cout << "\n";
        }

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
        FormulaT rightFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operandszz), carl::Relation::LEQ);

        // (x_1 - x_2 <= 0) && (y_1 - y_2 <= 0) -> (z_1 - z_2 <= 0)
        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, rightFormula);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "\n";
            cout << "created MonotonicityOne Axiom Formula is: " << finalFormula;
            cout << "\n";
        }

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
        FormulaT rightFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operandszz), carl::Relation::LESS);

        // (x_1 - x_2 < 0) && (y_1 - y_2 <= 0) && (y_2 != 0) -> (z_1 - z_2 < 0)
        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, rightFormula);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "\n";
            cout << "created MonotonicityTwo Axiom Formula is: " << finalFormula;
            cout << "\n";
        }

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
        FormulaT rightFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operandszz), carl::Relation::LESS);

        // (x_1 - x_2 <= 0) && (y_1 - y_2 < 0) && (x_2 != 0) -> (z_1 - z_2 < 0)
        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, rightFormula);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "\n";
            cout << "created MonotonicityThree Axiom Formula is: " << finalFormula;
            cout << "\n";
        }

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
        FormulaT rightFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operandszz), carl::Relation::EQ);

        // (x_1 - x_2 = 0) && (y_1 - y_2 = 0) -> (z_1 - z_2 = 0)
        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, rightFormula);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "\n";
            cout << "created Congruence Axiom Formula is: " << finalFormula;
            cout << "\n";
        }

        return finalFormula;
    }

    FormulaT createICPGreaterOne(VariableCapsule variableCapsule, RationalCapsule rationalCapsule){

        std::vector<Poly> operands1 {Poly(variableCapsule.getXVariable()), Poly(rationalCapsule.getARational())};
        FormulaT leftFormulaPartOneOne = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands1), carl::Relation::GEQ);

        std::vector<Poly> operands2 {Poly(variableCapsule.getYVariable()), Poly(rationalCapsule.getBRational())};
        FormulaT leftFormulaPartOneTwo = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands2), carl::Relation::GEQ);

        FormulaT leftFormulaOne = FormulaT(carl::FormulaType::AND, leftFormulaPartOneOne, leftFormulaPartOneTwo);

        FormulaT leftFormulaPartTwoOne = FormulaT(Poly(Poly::ConstructorOperation::ADD, operands1), carl::Relation::LEQ);

        FormulaT leftFormulaPartTwoTwo = FormulaT(Poly(Poly::ConstructorOperation::ADD, operands2), carl::Relation::LEQ);

        FormulaT leftFormulaTwo = FormulaT(carl::FormulaType::AND, leftFormulaPartTwoOne, leftFormulaPartTwoTwo);

        FormulaT leftFormula = FormulaT(carl::FormulaType::OR, leftFormulaOne, leftFormulaTwo);

        std::vector<Poly> operands3 {Poly(variableCapsule.getZVariable()), Poly(rationalCapsule.getCRational())};
        FormulaT rightFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands3), carl::Relation::GEQ);

        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, rightFormula);

        if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "created ICPGreaterOne Axiom Formula is: " << finalFormula << endl; }

        return finalFormula;
    }

    FormulaT createICPGreaterTwo(VariableCapsule variableCapsule, RationalCapsule rationalCapsule){

        std::vector<Poly> operands1 {Poly(variableCapsule.getXVariable()), Poly(rationalCapsule.getARational())};
        FormulaT leftFormulaPartOneOne = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands1), carl::Relation::GEQ);

        std::vector<Poly> operands2 {Poly(variableCapsule.getYVariable()), Poly(rationalCapsule.getBRational())};
        FormulaT leftFormulaPartOneTwo = FormulaT(Poly(Poly::ConstructorOperation::ADD, operands2), carl::Relation::LEQ);

        FormulaT leftFormulaOne = FormulaT(carl::FormulaType::AND, leftFormulaPartOneOne, leftFormulaPartOneTwo);

        FormulaT leftFormulaPartTwoOne = FormulaT(Poly(Poly::ConstructorOperation::ADD, operands1), carl::Relation::LEQ);

        FormulaT leftFormulaPartTwoTwo = FormulaT(Poly(Poly::ConstructorOperation::ADD, operands2), carl::Relation::GEQ);

        FormulaT leftFormulaTwo = FormulaT(carl::FormulaType::AND, leftFormulaPartTwoOne, leftFormulaPartTwoTwo);

        FormulaT leftFormula = FormulaT(carl::FormulaType::OR, leftFormulaOne, leftFormulaTwo);

        std::vector<Poly> operands3 {Poly(variableCapsule.getZVariable()), Poly(rationalCapsule.getCRational())};
        FormulaT rightFormula = FormulaT(Poly(Poly::ConstructorOperation::ADD, operands3), carl::Relation::LEQ);

        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, rightFormula);

        if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "created ICPGreaterTwo Axiom Formula is: " << finalFormula << endl; }

        return finalFormula;
    }

    FormulaT createICPLess(VariableCapsule variableCapsule, RationalCapsule rationalCapsule){

        FormulasT leftFormulas;

        std::vector<Poly> operands1 {-Poly(variableCapsule.getXVariable()), -Poly(rationalCapsule.getARational())};
        FormulaT leftFormulaPartOne = FormulaT(Poly(Poly::ConstructorOperation::ADD, operands1), carl::Relation::LEQ);
        leftFormulas.push_back(leftFormulaPartOne);

        std::vector<Poly> operands2 {Poly(variableCapsule.getXVariable()), Poly(rationalCapsule.getARational())};
        FormulaT leftFormulaPartTwo = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands2), carl::Relation::LEQ);
        leftFormulas.push_back(leftFormulaPartTwo);

        std::vector<Poly> operands3 {-Poly(variableCapsule.getYVariable()), -Poly(rationalCapsule.getBRational())};
        FormulaT leftFormulaPartThree = FormulaT(Poly(Poly::ConstructorOperation::ADD, operands3), carl::Relation::LEQ);
        leftFormulas.push_back(leftFormulaPartThree);

        std::vector<Poly> operands4 {Poly(variableCapsule.getYVariable()), Poly(rationalCapsule.getBRational())};
        FormulaT leftFormulaPartFour = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands4), carl::Relation::LEQ);
        leftFormulas.push_back(leftFormulaPartFour);

        FormulaT leftFormula = FormulaT(carl::FormulaType::AND, leftFormulas);

        std::vector<Poly> operands5 {-Poly(variableCapsule.getZVariable()), -Poly(rationalCapsule.getCRational())};
        FormulaT rightFormulaPartOne = FormulaT(Poly(Poly::ConstructorOperation::ADD, operands5), carl::Relation::LEQ);

        std::vector<Poly> operands6 {Poly(variableCapsule.getZVariable()), Poly(rationalCapsule.getCRational())};
        FormulaT rightFormulaPartTwo = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands6), carl::Relation::LEQ);

        FormulaT rightFormula = FormulaT(carl::FormulaType::AND, rightFormulaPartOne, rightFormulaPartTwo);

        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, rightFormula);

        if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "created ICPLess Axiom Formula is: " << finalFormula << endl; }

        return finalFormula;
    }

    bool abEqualcCheck(VariableCapsule variableCapsuleOuter, Model abstractModel){
        carl::Variable xVariable = variableCapsuleOuter.getXVariable();
        carl::Variable yVariable = variableCapsuleOuter.getYVariable();
        carl::Variable zVariable = variableCapsuleOuter.getZVariable();

        Rational aRational = abstractModel.find(variableCapsuleOuter.getXVariable())->second.asRational();
        Rational bRational = abstractModel.find(variableCapsuleOuter.getYVariable())->second.asRational();
        Rational cRational = abstractModel.find(variableCapsuleOuter.getZVariable())->second.asRational();

        if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << endl << "Found values in abEqualcCheck" << " Zvariable = " << cRational << " Xvariable = " << aRational << " Yvariable = " << bRational << endl; }

        carl::Variable aVariable = carl::freshRealVariable("a");
        carl::Variable bVariable = carl::freshRealVariable("b");
        carl::Variable cVariable = carl::freshRealVariable("c");

        Model abcModel;
        abcModel.emplace(aVariable, aRational);
        abcModel.emplace(bVariable, bRational);
        abcModel.emplace(cVariable, cRational);

        // c != a * b or, c - a * b != 0
        FormulaT abcFormula = FormulaT(Poly(cVariable) - Poly(aVariable*bVariable), carl::Relation::NEQ);

        if (carl::model::satisfiedBy(abcFormula, abcModel) == 1){
            return true;
        }

        return false;
    }

    bool abGreatercCheck(RationalCapsule rationalCapsule){

        carl::Variable aVariable = carl::freshRealVariable("a");
        carl::Variable bVariable = carl::freshRealVariable("b");
        carl::Variable cVariable = carl::freshRealVariable("c");

        Model abcModel;
        abcModel.emplace(aVariable, rationalCapsule.getARational());
        abcModel.emplace(bVariable, rationalCapsule.getBRational());
        abcModel.emplace(cVariable, rationalCapsule.getCRational());

        // c < a * b or, c - a * b < 0
        FormulaT abcFormula = FormulaT(Poly(cVariable) - Poly(aVariable*bVariable), carl::Relation::LESS);

        if (carl::model::satisfiedBy(abcFormula, abcModel) == 1){
            return true;
        }

        return false;
    }

    bool abLesscCheck(RationalCapsule rationalCapsule){

        carl::Variable aVariable = carl::freshRealVariable("a");
        carl::Variable bVariable = carl::freshRealVariable("b");
        carl::Variable cVariable = carl::freshRealVariable("c");

        Model abcModel;
        abcModel.emplace(aVariable, rationalCapsule.getARational());
        abcModel.emplace(bVariable, rationalCapsule.getBRational());
        abcModel.emplace(cVariable, rationalCapsule.getCRational());

        // c > a * b or, c - a * b > 0
        FormulaT abcFormula = FormulaT(Poly(cVariable) - Poly(aVariable*bVariable), carl::Relation::GREATER);

        if (carl::model::satisfiedBy(abcFormula, abcModel) == 1){
            return true;
        }

        return false;
    }

    FormulasT AxiomFactory::createFormula(AxiomType axiomType, Model abstractModel, MonomialMap monomialMap) {

        FormulasT formulas;

        for (MonomialMapIterator monomialIteratorOuter = monomialMap.begin(); monomialIteratorOuter != monomialMap.end(); ++monomialIteratorOuter){

            if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "creating variableCapsuleOuter..." << endl; }
            smtrat::VariableCapsule variableCapsuleOuter = extractVariables(monomialIteratorOuter);

            carl::Variable xVariable = variableCapsuleOuter.getXVariable();
            carl::Variable yVariable = variableCapsuleOuter.getYVariable();
            carl::Variable zVariable = variableCapsuleOuter.getZVariable();

            Rational aRational = abstractModel.find(variableCapsuleOuter.getXVariable())->second.asRational();
            Rational bRational = abstractModel.find(variableCapsuleOuter.getYVariable())->second.asRational();
            Rational cRational = abstractModel.find(variableCapsuleOuter.getZVariable())->second.asRational();

            RationalCapsule rationalCapsule(aRational, bRational, cRational);


            if (axiomType == AxiomType::ZERO) {
                formulas.push_back(createZeroOne(xVariable, yVariable, zVariable));
                formulas.push_back(createZeroTwo(xVariable, yVariable, zVariable));
                formulas.push_back(createZeroThree(xVariable, yVariable, zVariable));
            } else if (axiomType == AxiomType::TANGENT_PLANE){
                if(abEqualcCheck(variableCapsuleOuter, abstractModel)) {
                    if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "abEqualcCheck is true, creating TANGENT_PLANE..." << endl; }
                    if (xVariable != yVariable){
                        formulas.push_back(createTangentPlaneNEQOne(xVariable, yVariable, zVariable, aRational));
                        formulas.push_back(createTangentPlaneNEQTwo(xVariable, yVariable, zVariable, bRational));
                        formulas.push_back(createTangentPlaneNEQThree(xVariable, yVariable, zVariable, aRational, bRational));
                        formulas.push_back(createTangentPlaneNEQFour(xVariable, yVariable, zVariable, aRational, bRational));
                    } else {
                        formulas.push_back(createTangentPlaneEQOne(xVariable, yVariable, zVariable, aRational));
                        formulas.push_back(createTangentPlaneEQTwo(xVariable, yVariable, zVariable, aRational));
                    }
                } else {
                    if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "abEqualcCheck is false TANGENT_PLANE is not creating..." << endl; }
                }
            } else if(axiomType == AxiomType::MONOTONICITY || axiomType == AxiomType::CONGRUENCE){
                for (MonomialMapIterator monomialIteratorInner = monomialMap.begin(); monomialIteratorInner != monomialMap.end(); ++monomialIteratorInner){
                    if (monomialIteratorOuter == monomialIteratorInner){
                        continue;
                    }

                    if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "creating variableCapsuleInner..." << endl; }

                    smtrat::VariableCapsule variableCapsuleInner = extractVariables(monomialIteratorInner);

                    if (axiomType == AxiomType::MONOTONICITY){

                        if(abEqualcCheck(variableCapsuleInner, abstractModel) || abEqualcCheck(variableCapsuleOuter, abstractModel)){

                            if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "abEqualcCheck is true, creating Monotonicity..." << endl; }

                            formulas.push_back(createMonotonicityOne(variableCapsuleOuter, variableCapsuleInner));
                            formulas.push_back(createMonotonicityTwo(variableCapsuleOuter, variableCapsuleInner));
                            formulas.push_back(createMonotonicityThree(variableCapsuleOuter, variableCapsuleInner));

                        } else { if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "abEqualcCheck is false Monotonicity is not creating..." << endl; }}

                    } else if (axiomType == AxiomType::CONGRUENCE){

                        formulas.push_back(createCongruence(variableCapsuleOuter, variableCapsuleInner));

                    }
                }

            } else if (axiomType == AxiomType::ICP) {

                RationalCapsule rationalCapsuleAbs(carl::abs(rationalCapsule.getARational()), carl::abs(rationalCapsule.getBRational()), carl::abs(rationalCapsule.getCRational()));

                // NOTE: we assume a' = a, b' = b, c' = a * b. Here rationalCapsulePrime include the primes.
                RationalCapsule rationalCapsulePrime(rationalCapsuleAbs.getARational(), rationalCapsuleAbs.getBRational(), rationalCapsuleAbs.getARational() * rationalCapsuleAbs.getBRational());

                if (abGreatercCheck(rationalCapsuleAbs)){

                    if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "abGreatercCheck is true and ICP is creating..." << endl; }

                    formulas.push_back(createICPGreaterOne(variableCapsuleOuter, rationalCapsulePrime));
                    formulas.push_back(createICPGreaterTwo(variableCapsuleOuter, rationalCapsulePrime));

                } else if (abLesscCheck(rationalCapsuleAbs)) {

                    if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "abLesscCheck is true and ICP is creating..." << endl; }

                    formulas.push_back(createICPLess(variableCapsuleOuter, rationalCapsulePrime));

                } else {
                    if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "None of the precondition is true and ICP is not creating..." << endl; }
                }
            }
        }
        return formulas;
    }


}

