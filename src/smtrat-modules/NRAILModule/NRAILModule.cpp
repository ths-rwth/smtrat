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
#ifdef SMTRAT_DEVOPTION_Statistics
    , mStatistics(Settings::moduleName)
#endif

    template<class Settings>
    NRAILModule<Settings>::~NRAILModule()
    {}

    template<class Settings>
    bool NRAILModule<Settings>::informCore( const FormulaT& _constraint )
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
            cout << "inserting the monomial into the map:";
            cout << "\n";
            cout << "GeneratedVariable: " << GeneratedVariable << ", monomial: " << monomial;
            cout << "\n";
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
            cout << "the monomial, " << monomial << " alreday exists in the map!\nkey for this monomial in the map is, "
                 << retrievedVariable;
            cout << "\n";
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
    carl::Monomial::Arg monomialForEvenExponent(carl::Variable Variable, int exponent){

        int exponentToBe = divisionOfExponentByTwo(exponent);

        //carl::Variable GeneratedVariable = createZVariable();
        carl::Monomial::Arg monomialAsSquareOfVariable = createSquareOfVariable(Variable);

        //insertIntoMap(GeneratedVariable, monomialAsSquareOfVariable);
        carl::Variable newlyGeneratedOrOldVariable = insertIntoMapOrRetrieveExistingVariable(monomialAsSquareOfVariable);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "monomialForEvenExponent: Exponent of newly generated or old variable: " << exponentToBe;
            cout << "\n";
        }

        carl::Monomial::Arg newMonomial = carl::createMonomial(newlyGeneratedOrOldVariable, (carl::exponent)exponentToBe);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "monomialForEvenExponent: new Monomial: " << newMonomial;
            cout << "\n";
            cout << "\n";
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
    carl::Variable createLinearVariable(std::list<carl::Variable> variables){

        while (variables.size() > 1) {
            carl::Variable first = variables.front();
            variables.pop_front();

            carl::Variable second = variables.front();
            variables.pop_front();

            if (smtrat::LOG::getInstance().isDebugEnabled()) {
                cout << "first: " << first << "\n";
                cout << "second: " << second << "\n";
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
                cout << "createdMonomial: " << createdMonomial << "\n";
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
    carl::Monomial::Arg monomialForOddExponent(carl::Variable Variable, int exponent){

        std::list<carl::Variable> extraVariablesForOddExponenet;

        int exponentToBe = divisionOfExponentByTwo(exponent);
        //carl::Variable GeneratedVariable = createZVariable();
        carl::Monomial::Arg monomialAsSquareOfVariable = createSquareOfVariable(Variable);

        //insertIntoMap(GeneratedVariable, monomialAsSquareOfVariable);
        carl::Variable newlyGeneratedOrOldVariable = insertIntoMapOrRetrieveExistingVariable(monomialAsSquareOfVariable);

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "monomialForOddExponent: Exponent of newly generated or old variable: " << exponentToBe;
            cout << "\n";
        }

        carl::Monomial::Arg newMonomial = carl::createMonomial(newlyGeneratedOrOldVariable, (carl::exponent)exponentToBe);

        extraVariablesForOddExponenet.push_front(Variable);

        // get linear monomial
        while (!newMonomial->isLinear()) {
            if (smtrat::LOG::getInstance().isDebugEnabled()) {
                cout << "entering while" << "\n";
            }

            if(newMonomial->begin()->second % 2 == 0){

                newMonomial = monomialForEvenExponent(newMonomial->begin()->first, newMonomial->begin()->second);

            } else {
                newMonomial = monomialForOddExponent(newMonomial->begin()->first, newMonomial->begin()->second);
            }
        }

        // create newMonomial by multiplying newMonomial with the list extraVariablesForOddExponenet
        if(newMonomial->isLinear()) {
            carl::Variable variableOfNewMonomial =  newMonomial->begin()->first;
            if (smtrat::LOG::getInstance().isDebugEnabled()) {
                cout << "new monomial is linear" << "\n";
                cout << "variableOfNewMonomial: " << variableOfNewMonomial << "\n";
            }
            extraVariablesForOddExponenet.push_front(variableOfNewMonomial);
            if (smtrat::LOG::getInstance().isDebugEnabled()) {
                cout << "extraVariablesForOddExponenet: " << extraVariablesForOddExponenet << "\n";
            }
            newMonomial = carl::createMonomial((createLinearVariable(extraVariablesForOddExponenet)), (carl::exponent)1);
        }

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "monomialForOddExponent: new Monomial: " << newMonomial;
            cout << "\n";
            cout << "\n";
        }

        return newMonomial;
    }

    /**
     * create monomial which is linear
     * @param Variable a carl Variable object
     * @param exponent even or odd exponent of the variable
     * @return a linear monomial
     */
    carl::Monomial::Arg createLinearMonomial(carl::Variable Variable, int exponent)
    {
        carl::Monomial::Arg monomial;


        if(exponent == 1) {

            monomial = carl::createMonomial((Variable), (carl::exponent)1);

        } else if(exponent % 2 == 0){

            monomial = monomialForEvenExponent(Variable, exponent);

        } else {
            monomial = monomialForOddExponent(Variable, exponent);
        }


        if (monomial->nrVariables() == 1 && monomial->isLinear()) {

            if (smtrat::LOG::getInstance().isDebugEnabled()) {
                cout << "final Linear Monomial: " << monomial << " tDeg: " << monomial->tdeg();
                cout << "\n";
            }

            return monomial;
        }


        return createLinearMonomial(monomial->begin()->first, monomial->begin()->second);
    }

    /**
     * It linearizes a non-linear monomial
     * @param monomial a monomoal object
     * @return a linear variable
     */
    carl::Variable encapsulateMonomial(carl::Monomial::Arg monomial){

        std::list<carl::Variable> variables;

        carl::Variable finalVariable;

        for (auto it = monomial->begin(); it != monomial->end(); ++it) {

                carl::Monomial::Arg monomial = createLinearMonomial(it->first, it->second);

            if (smtrat::LOG::getInstance().isDebugEnabled()) {
                cout << "Received final Monomial is: " << monomial;
                cout << "\n";
                cout << "\n";
            }

                variables.push_back(monomial->begin()->first);
            }

            finalVariable = createLinearVariable(variables);

        return  finalVariable;
    }

    FormulaT linearization(FormulaT formula) {
        originalFormula->add(formula, true);

        //get constraint
        const ConstraintT& constraint = formula.constraint();

        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "\n";
            cout << "Constraint is: " << constraint;
            cout << "\n";
            cout << "\n";
        }

        //get polynomial(lhs) of constraint
        Poly poly = constraint.lhs();
        //counter of op[]
        int indexCount = 0;

        //size of array
        std::vector<Poly> op(poly.getTerms().size());

        // loops over each term and create linear polynomials
        for( auto& term : poly.getTerms() ) {

            if (!term.isConstant() && term.isLinear()) { //if the term is already linear and not a constant

                Poly p(term);
                op[indexCount] = p;

                if (smtrat::LOG::getInstance().isDebugEnabled()) {
                    cout << "Monomial is: " << term.monomial() << " (alreday linear)";
                    cout << "\n";
                    cout << "\n";
                }

            } else if (!term.isConstant()) { //if the term is a product of two or more variables

                //get monomial
                carl::Monomial::Arg monomial = term.monomial();

                if (smtrat::LOG::getInstance().isDebugEnabled()) {
                    cout << "Monomial is: " << monomial;
                    cout << "\n";
                }

                //get the linearized variable of the monomial
                carl::Variable finalVariable = encapsulateMonomial(monomial);

                //create new polynomial
                Poly p(term.coeff()*finalVariable);
                if (smtrat::LOG::getInstance().isDebugEnabled()) {
                    cout << "Generated MultiVariantPolynomial: " << p;
                    cout << "\n";
                    cout << "\n";
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
            cout << "Vector: " << op;
            cout << "\n";
        }

        //construction lhs of the constraint
        Poly finalPoly(Poly::ConstructorOperation::ADD,op);

        //create new formula
        FormulaT finalFormula = FormulaT(finalPoly, constraint.relation());
        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "Generated final Formula: " << finalFormula;
            cout << "\n";
            cout << "Generated New constraint: " << finalFormula.constraint();
            cout << "\n";
            cout << "\n";
        }

        return  finalFormula;
    }


    template<typename Settings>
    FormulaT NRAILModule<Settings>::linearizeSubformula(const FormulaT &formula)
    {
        if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "Formula from linearizeSubformula: " <<  formula << " Formula Type: " <<  formula.getType() << endl; }

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

            if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "Formula type is false and UNSAT! "; }

            mInfeasibleSubsets.push_back({formula});

            return false;
        }

        if (formula.getType() == carl::FormulaType::TRUE){
            if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "Formula type is true! "; }
            return true;
        }

        if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "Sub Formula: " <<  formula << " Sub Formula type: " <<  formula.getType() << endl; }

        FormulaT formulaFromVisitor = mVisitor.visitResult( formula, linearizeSubformulaFunction );

        if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "Generated  linearized Formula FromVisitor: " << formulaFromVisitor << endl; }
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
    void NRAILModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
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
     * Chekcs if the estimated model satisfies the input NRA formula.
     * @param estimatedModel The estimated model.
     */
    Answer isNRASatisfied(Model estimatedModel)
    {
        unsigned result = originalFormula->satisfiedBy(estimatedModel);
        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "Result " << result;
            cout << "\n";
        }
        return toAnswer(result);
    }

    /**
     * Creates the estimated model.
     * estimated model takes the solution from mModel or randomly chosen.
     * @param mModel Model of linearized formula.
     */
    Model createEstimatedModel(Model mModel){
        carl::Variables allVarsOfOriginalFormula;
        Model estimatedModel;

        //collect the variables into the container "allVarsOfOriginalFormula"
        originalFormula->vars(allVarsOfOriginalFormula);
        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "all variables of original formula: ";
            for (auto it = allVarsOfOriginalFormula.begin(); it != allVarsOfOriginalFormula.end(); ++it) {
                cout << it->name();
                cout << "   ";
            }
            cout << "\n";

            cout << "linearized variable | value: " << "\n";
            for (auto it = mModel.begin(); it != mModel.end(); ++it) {
                cout << it->first << " | " << it->second;
                cout << "\n";
            }
        }
        for (auto it1 = allVarsOfOriginalFormula.begin(); it1 != allVarsOfOriginalFormula.end(); ++it1) {
            int counter = 0;
            for (auto it2 = mModel.begin(); it2 != mModel.end(); ++it2) {
                if(it1->name() == it2->first.asVariable().name()){
                    estimatedModel.emplace(*it1, it2->second.asRational());
                    counter++;
                    break;
                }
            }
            if(counter == 0){
                estimatedModel.emplace(*it1, ZERO_RATIONAL);
            }
        }
        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "estimated model for original formula: " << "\n";
            for (auto it = estimatedModel.begin(); it != estimatedModel.end(); ++it) {
                cout << it->first << " | " << it->second;
                cout << "\n";
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
    Model createAbstractModel(Model mModel, Model estimatedModel){
        Model abstractModel;
        std::ostream stream(nullptr);
        stream.rdbuf(std::cout.rdbuf());

        for (auto mModelModelItarator = mModel.begin(); mModelModelItarator != mModel.end(); ++mModelModelItarator) {
            if (mModelModelItarator->second.isRational())
                abstractModel.emplace(mModelModelItarator->first, mModelModelItarator->second.asRational());
        }

        for (auto estimatedModelModelItarator = estimatedModel.begin(); estimatedModelModelItarator != estimatedModel.end(); ++estimatedModelModelItarator) {
            abstractModel.emplace(estimatedModelModelItarator->first, estimatedModelModelItarator->second.asRational());
        }

        MonomialMap monomialMap = smtrat::MonomialMappingByVariablePool::getInstance().getMMonomialMapping();
        for (MonomialMapIterator it = monomialMap.begin(); it != monomialMap.end(); ++it) {
            abstractModel.emplace(it->first, ZERO_RATIONAL);
        }
        if (smtrat::LOG::getInstance().isDebugEnabled()) {
            cout << "Abstract model for checking axioms: " << "\n";
            abstractModel.printOneline(stream, true);
            cout << "\n";
        }
        return abstractModel;
    }

    int rand(int min, int max) {
        std::time_t now = std::time(0);
        boost::random::mt19937 gen{static_cast<std::uint32_t>(now)};
        boost::random::uniform_int_distribution<> dist{min, max};
        return dist(gen);
    }

    FormulasT unsatisfiedFormulas(AxiomFactory::AxiomType axiomType, FormulasT formulas, Model model, UNSATFormulaSelectionStrategy formulaSelectionStrategy){

        if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "unsatisfiedFormulas to be check: " << formulas << endl; }

        if (axiomType == AxiomFactory::AxiomType::TANGENT_PLANE)
            return formulas;

        FormulasT unsatisfiedFormulas;
        for(FormulaT formula:formulas) {
            if (carl::model::satisfiedBy(formula, model) == 0){
                if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "unsatisfiedFormula: " << formula << endl; }
                unsatisfiedFormulas.push_back(formula);
                if (formulaSelectionStrategy == UNSATFormulaSelectionStrategy::FIRST){
                    if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "returning first formula" << endl; }
                    return unsatisfiedFormulas;
                }
            }
        }

        if (unsatisfiedFormulas.empty()) {
            return unsatisfiedFormulas;
        }

        if (formulaSelectionStrategy == UNSATFormulaSelectionStrategy::RANDOM) {
            std::vector<FormulaT> out;

            int min = unsatisfiedFormulas. size() / 2;
            int max = (unsatisfiedFormulas. size() * 80) / 100;

            size_t nelems = rand(min, max);

            if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "Selecting elements: " << nelems << " from the elemnts of: " << unsatisfiedFormulas.size() << endl; }
            std::sample(unsatisfiedFormulas.begin(), unsatisfiedFormulas.end(), std::back_inserter(out),
                        nelems, std::mt19937{std::random_device{}()});
            return out;
        }

        return unsatisfiedFormulas;
    }

    FormulasT refinement(AxiomFactory::AxiomType axiomType, Model abstractModel, UNSATFormulaSelectionStrategy formulaSelectionStrategy){

        FormulasT axiomFormulasToBeChecked = AxiomFactory::createFormula(axiomType, abstractModel, smtrat::MonomialMappingByVariablePool::getInstance().getMMonomialMapping());

        FormulasT unsatFormulas = unsatisfiedFormulas(axiomType, axiomFormulasToBeChecked, abstractModel, formulaSelectionStrategy);

        if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "pushing to unsatisfiedFormulas " << unsatFormulas << endl; }

        return  unsatFormulas;
    }


    template<class Settings>
    Answer NRAILModule<Settings>::checkCore()
    {
        std::ostream stream(nullptr);
        stream.rdbuf(std::cout.rdbuf());

        int loopCounter = 0;
        std::vector<AxiomFactory::AxiomType> axiomType(std::begin(Settings::axiomType), std::end(Settings::axiomType));

        int axiom_type_size = axiomType.size() - 1;

        if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "axiom_type_size: " << axiom_type_size << endl; }

        int axiomCounter = 0;

        bool isUnsatFormulasNotEmpty = true;

        Model abstractModel;

        while (true) {

            if (smtrat::LOG::getInstance().isDebugEnabled()) {
                cout << "Loop" << loopCounter << "\n";
                cout << "axiomCounter" << axiomCounter << "\n";
            }

            if(isUnsatFormulasNotEmpty) {

                if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "Calling backend for axiom counter = " << axiomCounter << endl; }

                auto AnswerOfLRA = runBackends();
                updateModel();

                if (smtrat::LOG::getInstance().isDebugEnabled()) {
                    cout << "Linearized Formula is AnswerOfLRA!" << AnswerOfLRA << "\n";
                }

                if (AnswerOfLRA != SAT) {

                    if (smtrat::LOG::getInstance().isDebugEnabled()) {cout << "Linearized Formula is Unsatisfied/Unknown!" << endl;}

                    if (AnswerOfLRA == UNSAT) {
                        generateTrivialInfeasibleSubset();
                    }
                    return AnswerOfLRA;
                }

                mModel = backendsModel();

                if (smtrat::LOG::getInstance().isDebugEnabled()) {
                    cout << "Solution/model of linearized formula: ";
                    mModel.printOneline(stream, true);
                    cout << "\n";
                    cout << "\n";
                }
                Model estimatedModel = createEstimatedModel(mModel);
                auto answerOfNRA = isNRASatisfied(estimatedModel);

                if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "answerOfNRA: " << answerOfNRA << endl; }

                if (answerOfNRA != UNSAT) {

                    if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "Input Formula is Satisfied!" << endl; }

                    if (smtrat::LOG::getInstance().isDebugEnabled()) { estimatedModel.printOneline(stream, true); }
                    return answerOfNRA;
                }

                abstractModel = createAbstractModel(mModel, estimatedModel);

            }

            FormulasT unsatFormulas = refinement(axiomType[axiomCounter], abstractModel, Settings::formulaSelectionStrategy);

            isUnsatFormulasNotEmpty = !unsatFormulas.empty();

            if (unsatFormulas.empty()) {
                if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "empty" << endl; }
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

        if (smtrat::LOG::getInstance().isDebugEnabled()) { cout << "Result is:" << endl; }

        return UNKNOWN; // This should be adapted according to your implementation.
    }

}

#include "Instantiation.h"
