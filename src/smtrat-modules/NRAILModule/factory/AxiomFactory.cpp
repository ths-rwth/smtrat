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
            std::cout << "\n";
            std::cout << "created ZeroOne Axiom Formula is: " << finalFormula;
            std::cout << "\n";
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
            std::cout << "\n";
            std::cout << "created ZeroTwo Axiom Formula is: " << finalFormula;
            std::cout << "\n";
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
            std::cout << "\n";
            std::cout << "created ZeroThree Axiom Formula is: " << finalFormula;
            std::cout << "\n";
        }

        return finalFormula;

    }

    FormulasT createZero(smtrat::VariableCapsule variableCapsule) {
        FormulasT zeroFormulas;
        zeroFormulas.push_back(createZeroOne(variableCapsule.getXVariable(), variableCapsule.getYVariable(), variableCapsule.getZVariable()));
        zeroFormulas.push_back(createZeroTwo(variableCapsule.getXVariable(), variableCapsule.getYVariable(), variableCapsule.getZVariable()));
        zeroFormulas.push_back(createZeroThree(variableCapsule.getXVariable(), variableCapsule.getYVariable(), variableCapsule.getZVariable()));
        return zeroFormulas;
    }

    FormulaT createTangentPlaneNEQOne (carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable, Rational aRational) {

        // x - a = 0
        FormulaT leftFormula = FormulaT(Poly(xVariable) - aRational, carl::Relation::EQ);

        // z - a*y = 0
        FormulaT rightFormula = FormulaT(Poly(zVariable) - Poly(aRational*yVariable), carl::Relation::EQ);

        // (x - a = 0) -> (z - a*y = 0)
        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, rightFormula);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "\n";
            std::cout << "created TangentPlaneNEQOne Axiom Formula is: " << finalFormula;
            std::cout << "\n";
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
            std::cout << "\n";
            std::cout << "created TangentPlaneNEQTwo Axiom Formula is: " << finalFormula;
            std::cout << "\n";
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
            std::cout << "\n";
            std::cout << "created TangentPlaneNEQThree Axiom Formula is: " << finalFormula;
            std::cout << "\n";
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
            std::cout << "\n";
            std::cout << "created TangentPlaneNEQFour Axiom Formula is: " << finalFormula;
            std::cout << "\n";
        }


        return finalFormula;

    }

    FormulasT createTangentPlaneNEQ(VariableCapsule variableCapsule, RationalCapsule rationalCapsule) {
        FormulasT tangentPlaneNEQ;
        tangentPlaneNEQ.push_back(createTangentPlaneNEQOne(variableCapsule.getXVariable(), variableCapsule.getYVariable(), variableCapsule.getZVariable(), rationalCapsule.getARational()));
        tangentPlaneNEQ.push_back(createTangentPlaneNEQTwo(variableCapsule.getXVariable(), variableCapsule.getYVariable(), variableCapsule.getZVariable(), rationalCapsule.getBRational()));
        tangentPlaneNEQ.push_back(createTangentPlaneNEQThree(variableCapsule.getXVariable(), variableCapsule.getYVariable(), variableCapsule.getZVariable(), rationalCapsule.getARational(), rationalCapsule.getBRational()));
        tangentPlaneNEQ.push_back(createTangentPlaneNEQFour(variableCapsule.getXVariable(), variableCapsule.getYVariable(), variableCapsule.getZVariable(), rationalCapsule.getARational(), rationalCapsule.getBRational()));
        return tangentPlaneNEQ;
    }

    FormulaT createTangentPlaneEQOne (carl::Variable xVariable, carl::Variable yVariable, carl::Variable zVariable, Rational aRational) {

        std::vector<Poly> operands {Poly(xVariable), Poly(aRational)};
        FormulaT leftFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands), carl::Relation::EQ);

        std::vector<Poly> operands2 {Poly(zVariable), Poly(aRational*yVariable)};
        FormulaT rightFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands2), carl::Relation::EQ);

        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, rightFormula);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "\n";
            std::cout << "created TangentPlaneEQOne Axiom Formula is: " << finalFormula;
            std::cout << "\n";
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
            std::cout << "\n";
            std::cout << "created TangentPlaneEQTwo Axiom Formula is: " << finalFormula;
            std::cout << "\n";
        }

        return finalFormula;

    }

    FormulasT createTangentPlaneEQ(VariableCapsule variableCapsule, RationalCapsule rationalCapsule) {
        FormulasT tangentPlaneEQ;
        tangentPlaneEQ.push_back(createTangentPlaneEQOne(variableCapsule.getXVariable(), variableCapsule.getYVariable(), variableCapsule.getZVariable(), rationalCapsule.getARational()));
        tangentPlaneEQ.push_back(createTangentPlaneEQTwo(variableCapsule.getXVariable(), variableCapsule.getYVariable(), variableCapsule.getZVariable(), rationalCapsule.getARational()));
        return tangentPlaneEQ;
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
            std::cout << "\n";
            std::cout << "zVariable is: " << zVariable;
            std::cout << "\n";
            std::cout << "xVariable is: " << xVariable;
            std::cout << "\n";
            std::cout << "yVariable is: " << yVariable;
            std::cout << "\n";
        }

        smtrat::VariableCapsule capsule(xVariable, yVariable, zVariable);
        return capsule;

    }

    Model createAbsoluteValuedModel(Model linearizedModel){

        Model absoluteValuedModel;

        for (auto it = linearizedModel.begin(); it != linearizedModel.end(); ++it) {

            Rational value = carl::abs(it->second.asRational());
            absoluteValuedModel.emplace(it->first, value);

        }

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "\n" << "absolute valued model: " << "\n";
            std::cout << "variable | value: " << "\n";
            for (auto it = absoluteValuedModel.begin(); it != absoluteValuedModel.end(); ++it) {
                std::cout << it->first << " | " << it->second;
                std::cout << "\n";
            }
        }

        return absoluteValuedModel;
    }

    /**
     * create an auxiliary variable e.g. aux_<Variable Name>
     * @param variable the variable for which auxiliary variable to be created
     * @return created auxiliary variable
     */
    carl::Variable createAuxiliaryVariable(carl::Variable variable){
        return carl::fresh_real_variable("aux_" + variable.name());
    }

    /**
     * | x1 | =
     * (and
     *     (=> (x1 >= 0) (y1 = x1))
     *     (=> (x1 < 0) (y1 = -x1))
     * )
     * @param variable
     * @return
     */
    FormulaT generateAbsFormula(carl::Variable variable, carl::Variable aux_variable) {

        FormulaT partOneOneFormula = FormulaT(Poly(variable), carl::Relation::GEQ);

        std::vector<Poly> operands {Poly(aux_variable), Poly(variable)};

        FormulaT partOneTwoFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands), carl::Relation::EQ);

        FormulaT partOneFormula = FormulaT(carl::FormulaType::IMPLIES, partOneOneFormula, partOneTwoFormula);

        FormulaT partTwoOneFormula = FormulaT(Poly(variable), carl::Relation::LESS);

        FormulaT partTwoTwoFormula = FormulaT(Poly(Poly::ConstructorOperation::ADD, operands), carl::Relation::EQ);

        FormulaT partTwoFormula = FormulaT(carl::FormulaType::IMPLIES, partTwoOneFormula, partTwoTwoFormula);

        FormulaT absFormula = FormulaT(carl::FormulaType::IMPLIES, partTwoOneFormula, partTwoTwoFormula);

        return absFormula;
    }


    /**
     *
     * | x1 | <= | x1 | =
     * (and
     *     (=> (x1 >= 0) (y1 = x1))
     *     (=> (x1 < 0) (y1 = -x1))
     *     (=> (x2 >= 0) (y2 = x2))
     *     (=> (x2 < 0) (y2 = -x2))
     *     (y1 <= y2)
     * )
     *
     * @param variableLeft
     * @param variableRight
     * @param relation
     * @return
     */
    FormulaT generateAbsFormula(carl::Variable variableLeft, carl::Variable variableRight, carl::Relation relation) {

        FormulasT formulas;

        carl::Variable auxLeft = createAuxiliaryVariable(variableLeft);

        FormulaT absFormulaOfVariable1 = generateAbsFormula(variableLeft, auxLeft);
        formulas.push_back(absFormulaOfVariable1);

        carl::Variable auxRight = createAuxiliaryVariable(variableRight);

        FormulaT absFormulaOfVariable2 = generateAbsFormula(variableRight, auxRight);
        formulas.push_back(absFormulaOfVariable2);

        std::vector<Poly> operands {Poly(auxLeft), Poly(auxRight)};

        FormulaT realtionFormula = FormulaT(Poly(Poly::ConstructorOperation::SUB, operands), relation);
        formulas.push_back(realtionFormula);

        FormulaT finalAbsFormula = FormulaT(carl::FormulaType::AND, formulas);

        return finalAbsFormula;
    }

    FormulaT createEquivalentToOriginalMonotonicityOne(smtrat::VariableCapsule variableCapsule,
                                                       smtrat::VariableCapsule variableCapsuleInner){

        FormulaT partOneLeftFormula = generateAbsFormula(variableCapsule.getXVariable(), variableCapsuleInner.getXVariable(), carl::Relation::LEQ);

        FormulaT partTwoLeftFormula = generateAbsFormula(variableCapsule.getYVariable(), variableCapsuleInner.getYVariable(), carl::Relation::LEQ);

        // (x_1 - x_2 <= 0) && (y_1 - y_2 <= 0)
        FormulaT leftFormula = FormulaT(carl::FormulaType::AND, partOneLeftFormula, partTwoLeftFormula);

        FormulaT rightFormula = generateAbsFormula(variableCapsule.getZVariable(), variableCapsuleInner.getZVariable(), carl::Relation::LEQ);

        // (x_1 - x_2 <= 0) && (y_1 - y_2 <= 0) -> (z_1 - z_2 <= 0)
        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, rightFormula);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "\n";
            std::cout << "created EquivalentToOriginalMonotonicityOne Axiom Formula is: " << finalFormula;
            std::cout << "\n";
        }

        return finalFormula;
    }

    FormulaT createEquivalentToOriginalMonotonicityTwo(smtrat::VariableCapsule variableCapsule, smtrat::VariableCapsule variableCapsuleInner){

        FormulaT partOneLeftFormula = generateAbsFormula(variableCapsule.getXVariable(), variableCapsuleInner.getXVariable(), carl::Relation::LESS);


        FormulaT partTwoLeftFormula = generateAbsFormula(variableCapsule.getYVariable(), variableCapsuleInner.getYVariable(), carl::Relation::LEQ);

        // y_2 != 0
        FormulaT partThreeLeftFormula = FormulaT(Poly(variableCapsuleInner.getYVariable()), carl::Relation::NEQ);

        // (x_1 - x_2 < 0) && (y_1 - y_2 <= 0) && (y_2 != 0)
        FormulaT leftFormula = FormulaT(carl::FormulaType::AND, partOneLeftFormula, partTwoLeftFormula, partThreeLeftFormula);

        FormulaT rightFormula = generateAbsFormula(variableCapsule.getZVariable(), variableCapsuleInner.getZVariable(), carl::Relation::LESS);

        // (x_1 - x_2 < 0) && (y_1 - y_2 <= 0) && (y_2 != 0) -> (z_1 - z_2 < 0)
        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, rightFormula);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "\n";
            std::cout << "created EquivalentToOriginalMonotonicityTwo Axiom Formula is: " << finalFormula;
            std::cout << "\n";
        }

        return finalFormula;
    }

    FormulaT createEquivalentToOriginalMonotonicityThree(smtrat::VariableCapsule variableCapsule,
                                                         smtrat::VariableCapsule variableCapsuleInner){

        FormulaT partOneLeftFormula = generateAbsFormula(variableCapsule.getXVariable(), variableCapsuleInner.getXVariable(), carl::Relation::LEQ);

        FormulaT partTwoLeftFormula = generateAbsFormula(variableCapsule.getYVariable(), variableCapsuleInner.getYVariable(), carl::Relation::LESS);

        // x_2 != 0
        FormulaT partThreeLeftFormula = FormulaT(Poly(variableCapsuleInner.getXVariable()), carl::Relation::NEQ);

        // (x_1 - x_2 <= 0) && (y_1 - y_2 < 0) && (x_2 != 0)
        FormulaT leftFormula = FormulaT(carl::FormulaType::AND, partOneLeftFormula, partTwoLeftFormula, partThreeLeftFormula);

        FormulaT rightFormula = generateAbsFormula(variableCapsule.getZVariable(), variableCapsuleInner.getZVariable(), carl::Relation::LESS);

        // (x_1 - x_2 <= 0) && (y_1 - y_2 < 0) && (x_2 != 0) -> (z_1 - z_2 < 0)
        FormulaT finalFormula = FormulaT(carl::FormulaType::IMPLIES, leftFormula, rightFormula);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "\n";
            std::cout << "created EquivalentToOriginalMonotonicityThree Axiom Formula is: " << finalFormula;
            std::cout << "\n";
        }

        return finalFormula;
    }

    RationalCapsule extractRationalCapsule(VariableCapsule variableCapsule, Model linearizedModel) {
        Rational aRational = linearizedModel.find(variableCapsule.getXVariable())->second.asRational();
        Rational bRational = linearizedModel.find(variableCapsule.getYVariable())->second.asRational();
        Rational cRational = linearizedModel.find(variableCapsule.getZVariable())->second.asRational();
        return  RationalCapsule(aRational, bRational, cRational);
    }

    FormulaT createOriginalMonotonicityOne(smtrat::VariableCapsule variableCapsule, smtrat::VariableCapsule variableCapsuleInner){
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

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "\n";
            std::cout << "created OriginalMonotonicityOne Axiom Formula is: " << finalFormula;
            std::cout << "\n";
        }

        return finalFormula;
    }

    FormulaT createOriginalMonotonicityTwo(smtrat::VariableCapsule variableCapsule, smtrat::VariableCapsule variableCapsuleInner){
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

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "\n";
            std::cout << "created OriginalMonotonicityTwo Axiom Formula is: " << finalFormula;
            std::cout << "\n";
        }

        return finalFormula;
    }

    FormulaT createOriginalMonotonicityThree(smtrat::VariableCapsule variableCapsule, smtrat::VariableCapsule variableCapsuleInner){
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

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "\n";
            std::cout << "created OriginalMonotonicityThree Axiom Formula is: " << finalFormula;
            std::cout << "\n";
        }

        return finalFormula;
    }

    FormulasT createMonotonicity(VariableCapsule variableCapsuleOuter, VariableCapsule variableCapsuleInner, Model absoluteValuedModel) {

        FormulasT monotonicityFormulas;

        if(carl::satisfied_by(createOriginalMonotonicityOne(variableCapsuleOuter, variableCapsuleInner), absoluteValuedModel) == 0){
            monotonicityFormulas.push_back(
                    createEquivalentToOriginalMonotonicityOne(variableCapsuleOuter, variableCapsuleInner));
        }

        if(carl::satisfied_by(createOriginalMonotonicityTwo(variableCapsuleOuter, variableCapsuleInner), absoluteValuedModel) == 0){
            monotonicityFormulas.push_back(
                    createEquivalentToOriginalMonotonicityTwo(variableCapsuleOuter, variableCapsuleInner));
        }

        if(carl::satisfied_by(createOriginalMonotonicityThree(variableCapsuleOuter, variableCapsuleInner), absoluteValuedModel) == 0){
            monotonicityFormulas.push_back(
                    createEquivalentToOriginalMonotonicityThree(variableCapsuleOuter, variableCapsuleInner));
        }

        return monotonicityFormulas;
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
            std::cout << "\n";
            std::cout << "created Congruence Axiom Formula is: " << finalFormula;
            std::cout << "\n";
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

        if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "created ICPGreaterOne Axiom Formula is: " << finalFormula << std::endl; }

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

        if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "created ICPGreaterTwo Axiom Formula is: " << finalFormula << std::endl; }

        return finalFormula;
    }

    FormulasT createICPGreater(VariableCapsule variableCapsule, RationalCapsule rationalCapsule) {
        FormulasT iCPGreater;
        iCPGreater.push_back(createICPGreaterOne(variableCapsule, rationalCapsule));
        iCPGreater.push_back(createICPGreaterTwo(variableCapsule, rationalCapsule));
        return iCPGreater;
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

        if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "created ICPLess Axiom Formula is: " << finalFormula << std::endl; }

        return finalFormula;
    }

    bool abEqualcCheck(VariableCapsule variableCapsuleOuter, Model linearizedModel){
        carl::Variable xVariable = variableCapsuleOuter.getXVariable();
        carl::Variable yVariable = variableCapsuleOuter.getYVariable();
        carl::Variable zVariable = variableCapsuleOuter.getZVariable();

        Rational aRational = linearizedModel.find(variableCapsuleOuter.getXVariable())->second.asRational();
        Rational bRational = linearizedModel.find(variableCapsuleOuter.getYVariable())->second.asRational();
        Rational cRational = linearizedModel.find(variableCapsuleOuter.getZVariable())->second.asRational();

        if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << std::endl << "Found values in abEqualcCheck" << " Zvariable = " << cRational << " Xvariable = " << aRational << " Yvariable = " << bRational << std::endl; }

        carl::Variable aVariable = carl::fresh_real_variable("a");
        carl::Variable bVariable = carl::fresh_real_variable("b");
        carl::Variable cVariable = carl::fresh_real_variable("c");

        Model abcModel;
        abcModel.emplace(aVariable, aRational);
        abcModel.emplace(bVariable, bRational);
        abcModel.emplace(cVariable, cRational);

        // c != a * b or, c - a * b != 0
        FormulaT abcFormula = FormulaT(Poly(cVariable) - Poly(aVariable*bVariable), carl::Relation::NEQ);

        if (carl::satisfied_by(abcFormula, abcModel) == 1){
            return true;
        }

        return false;
    }

    bool abGreatercCheck(RationalCapsule rationalCapsule){

        carl::Variable aVariable = carl::fresh_real_variable("a");
        carl::Variable bVariable = carl::fresh_real_variable("b");
        carl::Variable cVariable = carl::fresh_real_variable("c");

        Model abcModel;
        abcModel.emplace(aVariable, rationalCapsule.getARational());
        abcModel.emplace(bVariable, rationalCapsule.getBRational());
        abcModel.emplace(cVariable, rationalCapsule.getCRational());

        // c < a * b or, c - a * b < 0
        FormulaT abcFormula = FormulaT(Poly(cVariable) - Poly(aVariable*bVariable), carl::Relation::LESS);

        if (carl::satisfied_by(abcFormula, abcModel) == 1){
            return true;
        }

        return false;
    }

    bool abLesscCheck(RationalCapsule rationalCapsule){

        carl::Variable aVariable = carl::fresh_real_variable("a");
        carl::Variable bVariable = carl::fresh_real_variable("b");
        carl::Variable cVariable = carl::fresh_real_variable("c");

        Model abcModel;
        abcModel.emplace(aVariable, rationalCapsule.getARational());
        abcModel.emplace(bVariable, rationalCapsule.getBRational());
        abcModel.emplace(cVariable, rationalCapsule.getCRational());

        // c > a * b or, c - a * b > 0
        FormulaT abcFormula = FormulaT(Poly(cVariable) - Poly(aVariable*bVariable), carl::Relation::GREATER);

        if (carl::satisfied_by(abcFormula, abcModel) == 1){
            return true;
        }

        return false;
    }

    RationalCapsule generateAbcPrimeForICP(RationalCapsule rationalCapsule, bool isGreater) {

        Rational cByA = rationalCapsule.getCRational() / rationalCapsule.getARational();

        if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "generated cByA: " << cByA << std::endl; }

        RationalInterval bPrimeInterval;

        if (isGreater) {
            bPrimeInterval = RationalInterval(cByA, rationalCapsule.getBRational());
        } else {
            bPrimeInterval = RationalInterval(rationalCapsule.getBRational(), cByA);
        }

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "The bPrimeInterval is: " << bPrimeInterval << std::endl;
            if (bPrimeInterval.is_consistent())
                std::cout << "isConsistent: " << std::endl;
            if (!bPrimeInterval.is_empty())
                std::cout << "Not Empty: " << std::endl;
        }

        Rational bPrime = carl::sample(bPrimeInterval);

        Rational cByBPrime = rationalCapsule.getCRational() / bPrime;
        if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "generated cByBPrime: " << cByBPrime << std::endl; }

        RationalInterval aPrimeInterval;

        if (isGreater) {
            aPrimeInterval = RationalInterval(cByBPrime, rationalCapsule.getARational());
        } else {
            aPrimeInterval = RationalInterval(rationalCapsule.getARational(), cByBPrime);
        }

        Rational aPrime = carl::sample(aPrimeInterval);

        // c' = a * b
        Rational cPrime = aPrime * bPrime;

        if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "generated aPrime: " << aPrime << " bPrime: " << bPrime << " cPrime: " << cPrime << std::endl; }

        return  RationalCapsule(aPrime, bPrime, cPrime);
    }

    bool isAnyRationalIsZero (RationalCapsule rationalCapsule) {
        return carl::get_num(rationalCapsule.getARational()) == Rational(0) ||
                carl::get_num(rationalCapsule.getBRational()) == Rational(0) ||
                carl::get_num(rationalCapsule.getCRational()) == Rational(0);
    }


    FormulasT AxiomFactory::createFormula(AxiomType axiomType, Model linearizedModel, MonomialMap monomialMap) {


        Model absoluteValuedModel;

        if (axiomType == AxiomType::MONOTONICITY) { absoluteValuedModel = createAbsoluteValuedModel(linearizedModel); }

        FormulasT formulas;

        for (MonomialMapIterator monomialIteratorOuter = monomialMap.begin(); monomialIteratorOuter != monomialMap.end(); ++monomialIteratorOuter){

            if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << std::endl <<"creating variableCapsuleOuter..."; }
            smtrat::VariableCapsule variableCapsuleOuter = extractVariables(monomialIteratorOuter);

            RationalCapsule rationalCapsule = extractRationalCapsule(variableCapsuleOuter, linearizedModel);

            if (axiomType == AxiomType::ZERO) {

                FormulasT createdZeroFormulas = createZero(variableCapsuleOuter);
                formulas.insert(std::end(formulas), std::begin(createdZeroFormulas), std::end(createdZeroFormulas));

            } else if (axiomType == AxiomType::TANGENT_PLANE){
                if(abEqualcCheck(variableCapsuleOuter, linearizedModel)) {
                    if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "abEqualcCheck is true, creating TANGENT_PLANE..." << std::endl; }
                    if (variableCapsuleOuter.getXVariable() != variableCapsuleOuter.getYVariable()){
                        FormulasT createdTangentPlaneNEQ = createTangentPlaneNEQ(variableCapsuleOuter, rationalCapsule);
                        formulas.insert(std::end(formulas), std::begin(createdTangentPlaneNEQ), std::end(createdTangentPlaneNEQ));
                    } else {
                        FormulasT createdTangentPlaneEQ = createTangentPlaneEQ(variableCapsuleOuter, rationalCapsule);
                        formulas.insert(std::end(formulas), std::begin(createdTangentPlaneEQ), std::end(createdTangentPlaneEQ));
                    }
                } else {
                    if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "abEqualcCheck is false TANGENT_PLANE is not creating..." << std::endl; }
                }
            } else if(axiomType == AxiomType::MONOTONICITY || axiomType == AxiomType::CONGRUENCE){
                for (MonomialMapIterator monomialIteratorInner = monomialMap.begin(); monomialIteratorInner != monomialMap.end(); ++monomialIteratorInner){
                    if (monomialIteratorOuter == monomialIteratorInner){
                        continue;
                    }

                    if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << std::endl << "creating variableCapsuleInner..."; }

                    smtrat::VariableCapsule variableCapsuleInner = extractVariables(monomialIteratorInner);

                    if (axiomType == AxiomType::MONOTONICITY){

                        if(abEqualcCheck(variableCapsuleInner, linearizedModel) || abEqualcCheck(variableCapsuleOuter, linearizedModel)){

                            if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "abEqualcCheck is true, creating Monotonicity..." << std::endl; }

                            FormulasT createdMonotonicity = createMonotonicity(variableCapsuleOuter, variableCapsuleInner, absoluteValuedModel);
                            formulas.insert(std::end(formulas), std::begin(createdMonotonicity), std::end(createdMonotonicity));

                        } else { if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "abEqualcCheck is false Monotonicity is not creating..." << std::endl; }}

                    } else {

                        formulas.push_back(createCongruence(variableCapsuleOuter, variableCapsuleInner));

                    }
                }

            } else if (axiomType == AxiomType::ICP) {

                if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "ICP axioms are creating..." << std::endl; }

                // For ICP, we take the a, b, c always as positive value.
                RationalCapsule rationalCapsuleAbs(carl::abs(rationalCapsule.getARational()), carl::abs(rationalCapsule.getBRational()), carl::abs(rationalCapsule.getCRational()));

                if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "rationalCapsuleAbs for ICP with a: " << rationalCapsuleAbs.getARational() << " b: " << rationalCapsuleAbs.getBRational() << " c: " << rationalCapsuleAbs.getCRational() << std::endl; }

                if (isAnyRationalIsZero(rationalCapsuleAbs)){

                    if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "one of the rational is zero and Zero axiom is creating..." << std::endl; }

                    FormulasT createdZeroFormulas = createZero(variableCapsuleOuter);
                    formulas.insert(std::end(formulas), std::begin(createdZeroFormulas), std::end(createdZeroFormulas));

                } else {

                    if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "none of the rational is zero and ICP is creating..." << std::endl; }

                    if (abGreatercCheck(rationalCapsuleAbs)) {

                        if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "abGreatercCheck is true and ICPGreater is creating..." << std::endl; }

                        RationalCapsule rationalCapsulePrimeForICPGreater = generateAbcPrimeForICP(rationalCapsuleAbs, true);
                        // RationalCapsule rationalCapsulePrimeForICPGreater(rationalCapsuleAbs.getARational(), rationalCapsuleAbs.getBRational(), rationalCapsuleAbs.getARational() * rationalCapsuleAbs.getBRational());

                        FormulasT createdICPGreater = createICPGreater(variableCapsuleOuter, rationalCapsulePrimeForICPGreater);
                        formulas.insert(std::end(formulas), std::begin(createdICPGreater), std::end(createdICPGreater));

                    } else if (abLesscCheck(rationalCapsuleAbs)) {

                        if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "abLesscCheck is true and ICPLess is creating..." << std::endl; }

                        RationalCapsule rationalCapsulePrimeForICPLess = generateAbcPrimeForICP(rationalCapsuleAbs, false);
                        // RationalCapsule rationalCapsulePrimeForICPLess(rationalCapsuleAbs.getARational(), rationalCapsuleAbs.getBRational(), rationalCapsuleAbs.getARational() * rationalCapsuleAbs.getBRational());

                        formulas.push_back(createICPLess(variableCapsuleOuter, rationalCapsulePrimeForICPLess));

                    } else { if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "None of the precondition is true and ICP is not creating..." << std::endl; } }
                }
            }
        }
        return formulas;
    }


}

