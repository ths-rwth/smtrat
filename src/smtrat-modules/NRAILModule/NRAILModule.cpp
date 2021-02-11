/**
 * @file Abstract.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2018-07-12
 * Created on 2018-07-12.
 */

#include "NRAILModule.h"
#include "MonomialMappingByVariablePool.h"
#include "stdlib.h"
#include "factory/AxiomFactory.h"
#include "LOG.h"
#include <algorithm>
#include <iostream>
#include <random>
#include <vector>
#include "boost/random.hpp"
#include "boost/generator_iterator.hpp"


namespace smtrat
{
    template<class Settings>
    NRAILModule<Settings>::NRAILModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
            Module( _formula, _conditionals, _manager ),
            mVisitor()
    {
        linearizeSubformulaFunction = std::bind(&NRAILModule<Settings>::linearizeSubformula, this, std::placeholders::_1);
    }
    //mLRAFormula( new ModuleInput())

    template<class Settings>
    NRAILModule<Settings>::~NRAILModule()
    {}

    template<class Settings>
    bool NRAILModule<Settings>::informCore( const FormulaT& )
    {
        // Your code.
        return true; // This should be adapted according to your implementation.
    }

    template<class Settings>
    void NRAILModule<Settings>::init()
    {}

    int zVariableCounter = 0;
    std::string VariableName = "z_";
    ModuleInput* originalFormula( new ModuleInput());

    /**
     * create variables and each time increment the suffix e.g., z_0, z_1, etc.
     * @return a carl Variable object
     */
    carl::Variable createZVariable(){
        std::string GeneratedVariableName = VariableName + std::to_string(zVariableCounter++);
        return carl::freshRealVariable(GeneratedVariableName);
    }

    /**
     * create a square of the variable
     * @param Variable a carl Variable object e.g., x_0
     * @return a monomial object e.g., x_0^2
     */
    carl::Monomial::Arg createSquareOfVariable(carl::Variable Variable){
        return carl::createMonomial((Variable), (carl::exponent)2);
    }

    /**
     * Insert the variable as key with monomial as value into the map
     * The map is singeltone
     * @param GeneratedVariable
     * @param monomial
     */
    void insertIntoMap(carl::Variable GeneratedVariable, carl::Monomial::Arg monomial) {
        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "inserting the monomial into the map:";
            std::cout << "\n";
            std::cout << "GeneratedVariable: " << GeneratedVariable << ", monomial: " << monomial;
            std::cout << "\n";
        }
        smtrat::MonomialMappingByVariablePool::getInstance().insertMonomialMapping(GeneratedVariable, monomial);
    }

    int divisionOfExponentByTwo(int exponent){
        return (int)(exponent / 2);
    }

    /**
     * Check if the monomial is alreday inserted imto the map,
     * If yes, returned the key which is a variable otherwise create new variable
     * and insert the monomial into the map against this new variable
     * @param monomial a monomoal object
     * @return a carl::Variable object
     */
    carl::Variable insertIntoMapOrRetrieveExistingVariable(carl::Monomial::Arg monomial){

        carl::Variable retrievedVariable = smtrat::MonomialMappingByVariablePool::getInstance().variable(monomial);

        if(smtrat::MonomialMappingByVariablePool::getInstance().isNull(retrievedVariable)){
            //create new variable as it doesn't exist in the map
            carl::Variable GeneratedVariable = createZVariable();
            //insert into the map
            insertIntoMap(GeneratedVariable, monomial);

            return GeneratedVariable;
        }

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "the monomial, " << monomial << " alreday exists in the map!\nkey for this monomial in the map is, "
                 << retrievedVariable;
            std::cout << "\n";
        }

        return retrievedVariable;

    }

    /**
     * Replace square of variable (x_0^2) of a monomial (x_0^6) by a variable (z_0),
     * create a new monomial (z_0^3)
     * and insert this variable as key with monomial (x_0^2) as value in the map
     * @param Variable a carl::Variable object
     * @param exponent an even exponent
     * @return new monomial
     */
    carl::Monomial::Arg abstractUnivariateMonomialForEvenExponent(carl::Variable Variable, int exponent){

        int exponentToBe = divisionOfExponentByTwo(exponent);

        //carl::Variable GeneratedVariable = createZVariable();
        carl::Monomial::Arg monomialAsSquareOfVariable = createSquareOfVariable(Variable);

        //insertIntoMap(GeneratedVariable, monomialAsSquareOfVariable);
        carl::Variable newlyGeneratedOrOldVariable = insertIntoMapOrRetrieveExistingVariable(monomialAsSquareOfVariable);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "abstractUnivariateMonomialForEvenExponent: Exponent of newly generated or old variable: " << exponentToBe;
            std::cout << "\n";
        }

        carl::Monomial::Arg newMonomial = carl::createMonomial(newlyGeneratedOrOldVariable, (carl::exponent)exponentToBe);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "abstractUnivariateMonomialForEvenExponent: new Monomial: " << newMonomial;
            std::cout << "\n";
            std::cout << "\n";
        }

        return newMonomial;
    }

    /**
     * It creates monomial by taking and popping first two items from the list,
     * Insert this new monomial as value into the map against a newly generated variable,
     * Each time the newly generated variable is insterted at the front of the list
     * @param variables List of carl variables
     * @return created new linear variable
     */
    carl::Variable abstractProductRecursively(std::list<carl::Variable> variables){

        while (variables.size() > 1) {
            carl::Variable first = variables.front();
            variables.pop_front();

            carl::Variable second = variables.front();
            variables.pop_front();

            if (smtrat::LOG::getInstance().isDebugEnabled()) {
                std::cout << "first: " << first << "\n";
                std::cout << "second: " << second << "\n";
            }

            // variables must be sorted to create monomial.
            carl::Monomial::Content mExponents(std::initializer_list<std::pair<carl::Variable, carl::exponent>>
             (
                 {std::make_pair(first,(carl::exponent)1), std::make_pair(second, (carl::exponent)1)}
              ));

            std::sort(mExponents.begin(), mExponents.end(), [](const std::pair<carl::Variable, carl::uint>& p1, const std::pair<carl::Variable, carl::uint>& p2){ return p1.first < p2.first; });

            carl::Monomial::Arg createdMonomial = carl::createMonomial(std::initializer_list<std::pair<carl::Variable, carl::exponent>>
           (
                   {mExponents[0], mExponents[1]}
           ),
           (carl::exponent)(2));

            if (smtrat::LOG::getInstance().isDebugEnabled()) {
                std::cout << "createdMonomial: " << createdMonomial << "\n";
            }

            //carl::Variable GeneratedVariable = createZVariable();
            carl::Variable newlyGeneratedOrOldVariable = insertIntoMapOrRetrieveExistingVariable(createdMonomial);
            //insertIntoMap(GeneratedVariable, createdMonomial);

            variables.push_front(newlyGeneratedOrOldVariable);

        }

        return variables.front();
    }


    /**
     * Replace square of variable (x_0^2) of a monomial (x_0^7) by a variable (z_0),
     * create a linear monomial (z_1)
     * and insert the variable as key with monomial as value in the map
     * @param Variable a carl::Variable object
     * @param exponent an odd exponent
     * @return new linear monomial
     */
    carl::Monomial::Arg abstractUnivariateMonomialForOddExponent(carl::Variable Variable, int exponent){

        std::list<carl::Variable> extraVariablesForOddExponenet;

        int exponentToBe = divisionOfExponentByTwo(exponent);
        //carl::Variable GeneratedVariable = createZVariable();
        carl::Monomial::Arg monomialAsSquareOfVariable = createSquareOfVariable(Variable);

        //insertIntoMap(GeneratedVariable, monomialAsSquareOfVariable);
        carl::Variable newlyGeneratedOrOldVariable = insertIntoMapOrRetrieveExistingVariable(monomialAsSquareOfVariable);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "abstractUnivariateMonomialForOddExponent: Exponent of newly generated or old variable: " << exponentToBe;
            std::cout << "\n";
        }

        carl::Monomial::Arg newMonomial = carl::createMonomial(newlyGeneratedOrOldVariable, (carl::exponent)exponentToBe);

        extraVariablesForOddExponenet.push_front(Variable);

        // get linear monomial
        while (!newMonomial->isLinear()) {
            if (smtrat::LOG::getInstance().isDebugEnabled()) {
                std::cout << "entering while" << "\n";
            }

            if(newMonomial->begin()->second % 2 == 0){

                newMonomial = abstractUnivariateMonomialForEvenExponent(newMonomial->begin()->first,
                                                                        newMonomial->begin()->second);

            } else {
                newMonomial = abstractUnivariateMonomialForOddExponent(newMonomial->begin()->first,
                                                                       newMonomial->begin()->second);
            }
        }

        // create newMonomial by multiplying newMonomial with the list extraVariablesForOddExponenet
        if(newMonomial->isLinear()) {
            carl::Variable variableOfNewMonomial =  newMonomial->begin()->first;
            if (smtrat::LOG::getInstance().isDebugEnabled()) {
                std::cout << "new monomial is linear" << "\n";
                std::cout << "variableOfNewMonomial: " << variableOfNewMonomial << "\n";
            }
            extraVariablesForOddExponenet.push_front(variableOfNewMonomial);
            if (smtrat::LOG::getInstance().isDebugEnabled()) {
                std::cout << "extraVariablesForOddExponenet: " << extraVariablesForOddExponenet << "\n";
            }
            newMonomial = carl::createMonomial((abstractProductRecursively(extraVariablesForOddExponenet)), (carl::exponent)1);
        }

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "abstractUnivariateMonomialForOddExponent: new Monomial: " << newMonomial;
            std::cout << "\n";
            std::cout << "\n";
        }

        return newMonomial;
    }

    /**
     * create monomial which is linear
     * @param Variable a carl Variable object
     * @param exponent even or odd exponent of the variable
     * @return a linear monomial
     */
    carl::Monomial::Arg abstractUnivariateMonomial (carl::Variable Variable, int exponent)
    {
        carl::Monomial::Arg monomial;


        if(exponent == 1) {

            monomial = carl::createMonomial((Variable), (carl::exponent)1);

        } else if(exponent % 2 == 0){

            monomial = abstractUnivariateMonomialForEvenExponent(Variable, exponent);

        } else {
            monomial = abstractUnivariateMonomialForOddExponent(Variable, exponent);
        }


        if (monomial->nrVariables() == 1 && monomial->isLinear()) {

            if (smtrat::LOG::getInstance().isDebugEnabled()) {
                std::cout << "final Linear Monomial: " << monomial << " tDeg: " << monomial->tdeg();
                std::cout << "\n";
            }

            return monomial;
        }


        return abstractUnivariateMonomial(monomial->begin()->first, monomial->begin()->second);
    }

    /**
     * It linearizes a non-linear monomial
     * @param monomial a monomoal object
     * @return a linear variable
     */
    carl::Variable abstractMonomial(carl::Monomial::Arg monomial){

        std::list<carl::Variable> variables;

        carl::Variable finalVariable;

        for (auto it = monomial->begin(); it != monomial->end(); ++it) {

                carl::Monomial::Arg monomial = abstractUnivariateMonomial(it->first, it->second);

            if (smtrat::LOG::getInstance().isDebugEnabled()) {
                std::cout << "Received final Monomial is: " << monomial;
                std::cout << "\n";
                std::cout << "\n";
            }

                variables.push_back(monomial->begin()->first);
            }

            finalVariable = abstractProductRecursively(variables);

        return  finalVariable;
    }

    FormulaT linearization(FormulaT formula) {
        originalFormula->add(formula, true);

        //get constraint
        const ConstraintT& constraint = formula.constraint();

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "\n";
            std::cout << "Constraint is: " << constraint;
            std::cout << "\n";
            std::cout << "\n";
        }

        //get polynomial(lhs) of constraint
        Poly poly = constraint.lhs();
        //counter of op[]
        std::size_t indexCount = 0;

        //size of array
        std::vector<Poly> op(poly.getTerms().size());

        // loops over each term and create linear polynomials
        for( auto& term : poly.getTerms() ) {

            if (!term.isConstant() && term.isLinear()) { //if the term is already linear and not a constant

                Poly p(term);
                op[indexCount] = p;

                if (smtrat::LOG::getInstance().isDebugEnabled()) {
                    std::cout << "Monomial is: " << term.monomial() << " (alreday linear)";
                    std::cout << "\n";
                    std::cout << "\n";
                }

            } else if (!term.isConstant()) { //if the term is a product of two or more variables

                //get monomial
                carl::Monomial::Arg monomial = term.monomial();

                if (smtrat::LOG::getInstance().isDebugEnabled()) {
                    std::cout << "Monomial is: " << monomial;
                    std::cout << "\n";
                }

                //get the linearized variable of the monomial
                carl::Variable finalVariable = abstractMonomial(monomial);

                //create new polynomial
                Poly p(term.coeff()*finalVariable);
                if (smtrat::LOG::getInstance().isDebugEnabled()) {
                    std::cout << "Generated MultiVariantPolynomial: " << p;
                    std::cout << "\n";
                    std::cout << "\n";
                }
                op[indexCount] = p;

            } else { //if the term is a constants

                //create new polynomial
                Poly p(term);
                op[indexCount] = p;

            }

            indexCount++;
        }

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "Vector: " << op;
            std::cout << "\n";
        }

        //construction lhs of the constraint
        Poly finalPoly(Poly::ConstructorOperation::ADD,op);

        //create new formula
        FormulaT finalFormula = FormulaT(finalPoly, constraint.relation());
        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "Generated final Formula: " << finalFormula;
            std::cout << "\n";
            std::cout << "Generated New constraint: " << finalFormula.constraint();
            std::cout << "\n";
            std::cout << "\n";
        }

        return  finalFormula;
    }


    template<typename Settings>
    FormulaT NRAILModule<Settings>::linearizeSubformula(const FormulaT &formula)
    {
        if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "Formula from linearizeSubformula: " <<  formula << " Formula Type: " <<  formula.getType() << std::endl; }

        if (formula.getType() == carl::FormulaType::CONSTRAINT) {
            FormulaT linearizedFormula = linearization(formula);
            return linearizedFormula;
        }

        return formula;
    }


    template<class Settings>
    bool NRAILModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        const FormulaT& formula{_subformula->formula()};

        if (formula.getType() == carl::FormulaType::FALSE){

            if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "Formula type is false and UNSAT! "; }

            mInfeasibleSubsets.push_back({formula});

            return false;
        }

        if (formula.getType() == carl::FormulaType::TRUE){
            if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "Formula type is true! "; }
            return true;
        }

        if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "Sub Formula: " <<  formula << " Sub Formula type: " <<  formula.getType() << std::endl; }

        FormulaT formulaFromVisitor = mVisitor.visitResult( formula, linearizeSubformulaFunction );

        if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "Generated  linearized Formula FromVisitor: " << formulaFromVisitor << std::endl; }
        ////////////////////////////////////////////////
        //
        // Adding the Linearized Formula to the global
        // ModuleInput type variable. This global
        // variable will be used to add all of the
        // Linearized formulas to the passed formula
        //
        ////////////////////////////////////////////////
        addSubformulaToPassedFormula(formulaFromVisitor);

        return true; // This should be adapted according to your implementation.
    }

    template<class Settings>
    void NRAILModule<Settings>::removeCore( ModuleInput::const_iterator )
    {
        // Your code.
    }

    template<class Settings>
    void NRAILModule<Settings>::updateModel() const
    {
        mModel.clear();
        if( solverState() == Answer::SAT )
        {
            // Your code.
        }
    }

    Answer toAnswer(int value){
        if(value == 0){
            return Answer::UNSAT;
        } else if(value == 1) {
            return Answer::SAT;
        } else {
            return Answer::UNKNOWN;
        }
    }

    /**
     * Chekcs if the estimated Assignment satisfies the input NRA formula.
     * @param estimatedModel The estimated model.
     */
    Answer isNRASatisfied(Model estimatedModel)
    {
        unsigned result = originalFormula->satisfiedBy(estimatedModel);
        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "Result " << result;
            std::cout << "\n";
        }
        return toAnswer(result);
    }

    /**
     * Creates the estimated model.
     * estimated model takes the solution from mModel or randomly chosen.
     * @param linearizedModel Model of linearized formula.
     */
    Model createEstimatedAssignment(Model linearizedModel){
        Model estimatedModel;

        //collect the variables into the container "allVarsOfOriginalFormula"
        carl::carlVariables _vars;
        originalFormula->gatherVariables(_vars);
        auto allVarsOfOriginalFormula = _vars.underlyingVariables(); // TODO VARREFACTOR
        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "all variables of original formula: ";
            for (auto it = allVarsOfOriginalFormula.begin(); it != allVarsOfOriginalFormula.end(); ++it) {
                std::cout << it->name();
                std::cout << "   ";
            }
            std::cout << "\n";

            std::cout << "linearized variable | value: " << "\n";
            for (auto it = linearizedModel.begin(); it != linearizedModel.end(); ++it) {
                std::cout << it->first << " | " << it->second;
                std::cout << "\n";
            }
        }
        for (auto it1 = allVarsOfOriginalFormula.begin(); it1 != allVarsOfOriginalFormula.end(); ++it1) {
            int counter = 0;
            for (auto it2 = linearizedModel.begin(); it2 != linearizedModel.end(); ++it2) {
                if(it1->name() == it2->first.asVariable().name()){
                    estimatedModel.emplace(*it1, it2->second.asRational());
                    counter++;
                    break;
                }
            }
            if(counter == 0){
                estimatedModel.emplace(*it1, Rational(0));
            }
        }
        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "estimated model for original formula: " << "\n";
            for (auto it = estimatedModel.begin(); it != estimatedModel.end(); ++it) {
                std::cout << it->first << " | " << it->second;
                std::cout << "\n";
            }
        }
        return estimatedModel;
    }

    /**
     * create a model combining mModel, estimatedModel and rest of the variables are guessed.
     * This model checks the satifiability of the axioms.
     * @param mModel Model of linearized formula.
     * @param estimatedModel the estimated model for original formula.
     * @return the Abstract Model
     */
    Model extendLinearizedModel(Model mModel, Model estimatedModel){
        Model linearizedModel;
        std::ostream stream(nullptr);
        stream.rdbuf(std::cout.rdbuf());

        for (auto mModelItarator = mModel.begin(); mModelItarator != mModel.end(); ++mModelItarator) {
            if (mModelItarator->second.isRational())
                linearizedModel.emplace(mModelItarator->first, mModelItarator->second.asRational());
        }

        for (auto estimatedModelItarator = estimatedModel.begin(); estimatedModelItarator != estimatedModel.end(); ++estimatedModelItarator) {
            linearizedModel.emplace(estimatedModelItarator->first, estimatedModelItarator->second.asRational());
        }

        MonomialMap monomialMap = smtrat::MonomialMappingByVariablePool::getInstance().getMMonomialMapping();
        for (MonomialMapIterator it = monomialMap.begin(); it != monomialMap.end(); ++it) {
            linearizedModel.emplace(it->first, Rational(0));
        }
        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            std::cout << "Abstract model for checking axioms: " << "\n";
            linearizedModel.printOneline(stream, true);
            std::cout << "\n";
        }
        return linearizedModel;
    }

    int rand(int min, int max) {
        std::time_t now = std::time(0);
        boost::random::mt19937 gen{static_cast<std::uint32_t>(now)};
        boost::random::uniform_int_distribution<> dist{min, max};
        return dist(gen);
    }

    FormulasT unsatisfiedFormulas(AxiomFactory::AxiomType axiomType, FormulasT formulas, Model model, UNSATFormulaSelectionStrategy formulaSelectionStrategy){

        if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "unsatisfiedFormulas to be check: " << formulas << std::endl; }

        FormulasT unsatisfiedFormulas;

        if (axiomType == AxiomFactory::AxiomType::TANGENT_PLANE || axiomType == AxiomFactory::AxiomType::MONOTONICITY) {
            for(FormulaT formula:formulas) {
                if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "unsatisfiedFormula: " << formula << std::endl; }
                unsatisfiedFormulas.push_back(formula);
                if (formulaSelectionStrategy == UNSATFormulaSelectionStrategy::FIRST){
                    if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "returning first formula" << std::endl; }
                    return unsatisfiedFormulas;
                }
            }
        } else {
            for(FormulaT formula:formulas) {
                if (carl::model::satisfiedBy(formula, model) == 0){
                    if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "unsatisfiedFormula: " << formula << std::endl; }
                    unsatisfiedFormulas.push_back(formula);
                    if (formulaSelectionStrategy == UNSATFormulaSelectionStrategy::FIRST){
                        if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "returning first formula" << std::endl; }
                        return unsatisfiedFormulas;
                    }
                }
            }
        }
        if (unsatisfiedFormulas.empty()) {
            return unsatisfiedFormulas;
        }

        int unsatisfiedFormulasSize = unsatisfiedFormulas. size();

        if (formulaSelectionStrategy == UNSATFormulaSelectionStrategy::RANDOM) {
            std::vector<FormulaT> randomlySelectedFormulas;

            int min = unsatisfiedFormulasSize / 2;
            int max = (unsatisfiedFormulasSize * 80) / 100;

            size_t nelems = rand(min, max);

            if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "Selecting elements: " << nelems << " from the elemnts of: " << unsatisfiedFormulasSize << std::endl; }
            std::sample(unsatisfiedFormulas.begin(), unsatisfiedFormulas.end(), std::back_inserter(randomlySelectedFormulas),
                        nelems, std::mt19937{std::random_device{}()});
            return randomlySelectedFormulas;
        }

        return unsatisfiedFormulas;
    }

    FormulasT refinement(AxiomFactory::AxiomType axiomType, Model linearizedModel, UNSATFormulaSelectionStrategy formulaSelectionStrategy){

        FormulasT axiomFormulasToBeChecked = AxiomFactory::createFormula(axiomType, linearizedModel, smtrat::MonomialMappingByVariablePool::getInstance().getMMonomialMapping());

        FormulasT unsatFormulas = unsatisfiedFormulas(axiomType, axiomFormulasToBeChecked, linearizedModel, formulaSelectionStrategy);

        if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "pushing to unsatisfiedFormulas " << unsatFormulas << std::endl; }

        return  unsatFormulas;
    }


    template<class Settings>
    Answer NRAILModule<Settings>::checkCore()
    {
        std::ostream stream(nullptr);
        stream.rdbuf(std::cout.rdbuf());

        int loopCounter = 0;
        std::vector<AxiomFactory::AxiomType> axiomType(std::begin(Settings::axiomType), std::end(Settings::axiomType));

		assert(axiomType.size() > 0);
        std::size_t axiom_type_size = axiomType.size() - 1;

        if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "axiom_type_size: " << axiom_type_size << std::endl; }

        std::size_t axiomCounter = 0;

        bool isUnsatFormulasNotEmpty = true;

        Model linearizedModel;

        while (true) {

            if (smtrat::LOG::getInstance().isDebugEnabled()) {
                std::cout << "Loop" << loopCounter << "\n";
                std::cout << "axiomCounter" << axiomCounter << "\n";
            }

            if(isUnsatFormulasNotEmpty) {

                if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "Calling backend for axiom counter = " << axiomCounter << std::endl; }

                auto AnswerOfLRA = runBackends();
                updateModel();

                if (smtrat::LOG::getInstance().isDebugEnabled()) {
                    std::cout << "Linearized Formula is AnswerOfLRA!" << AnswerOfLRA << "\n";
                }

                if (AnswerOfLRA != SAT) {

                    if (smtrat::LOG::getInstance().isDebugEnabled()) {std::cout << "Linearized Formula is Unsatisfied/Unknown!" << std::endl;}

                    if (AnswerOfLRA == UNSAT) {
                        generateTrivialInfeasibleSubset();
                    }
                    return AnswerOfLRA;
                }
                // NOTE: This mModel is the actual linearized model.
                mModel = backendsModel();

                if (smtrat::LOG::getInstance().isDebugEnabled()) {
                    std::cout << "Solution/model of linearized formula: ";
                    mModel.printOneline(stream, true);
                    std::cout << "\n";
                    std::cout << "\n";
                }
                Model estimatedModel = createEstimatedAssignment(mModel);
                auto answerOfNRA = isNRASatisfied(estimatedModel);

                if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "answerOfNRA: " << answerOfNRA << std::endl; }

                if (answerOfNRA != UNSAT) {

                    if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "Input Formula is Satisfied!" << std::endl; }

                    if (smtrat::LOG::getInstance().isDebugEnabled()) { estimatedModel.printOneline(stream, true); }
                    return answerOfNRA;
                }
                // NOTE: mModel is the actual linearized model, linearizedModel contains linearized model with estimatedAssignments
                linearizedModel = extendLinearizedModel(mModel, estimatedModel);

            }

            FormulasT unsatFormulas = refinement(axiomType[axiomCounter], linearizedModel, Settings::formulaSelectionStrategy);

            isUnsatFormulasNotEmpty = !unsatFormulas.empty();

            if (unsatFormulas.empty()) {
                if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "empty" << std::endl; }
            }

            for (FormulaT formulaT : unsatFormulas) {
                addSubformulaToPassedFormula(formulaT);
            }


            if (axiomCounter == axiom_type_size) {
                axiomCounter = 0;
            } else {
                axiomCounter++;
            }

            loopCounter++;
        }

        if (smtrat::LOG::getInstance().isDebugEnabled()) { std::cout << "Result is:" << std::endl; }

        return UNKNOWN; // This should be adapted according to your implementation.
    }

}

#include "Instantiation.h"
