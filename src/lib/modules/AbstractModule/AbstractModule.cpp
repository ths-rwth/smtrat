/**
 * @file Abstract.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2018-07-12
 * Created on 2018-07-12.
 */

#include "AbstractModule.h"
#include "MonomialMappingByVariablePool.h"

namespace smtrat
{
    template<class Settings>
    AbstractModule<Settings>::AbstractModule(const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager):
            Module( _formula, _conditionals, _manager )
#ifdef SMTRAT_DEVOPTION_Statistics
    , mStatistics(Settings::moduleName)
#endif
    {}

    template<class Settings>
    AbstractModule<Settings>::~AbstractModule()
    {}

    template<class Settings>
    bool AbstractModule<Settings>::informCore( const FormulaT& _constraint )
    {
        // Your code.
        return true; // This should be adapted according to your implementation.
    }

    template<class Settings>
    void AbstractModule<Settings>::init()
    {}

    int zVariableCounter = 0;
    std::string VariableName = "z_";

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
        cout << "inserting the monomial into the map:";
        cout << "\n";
        cout << "GeneratedVariable: " << GeneratedVariable << ", monomial: " << monomial;
        cout << "\n";
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

        cout << "the monomial, " << monomial << " alreday exists in the map!\nkey for this monomial in the map is, " << retrievedVariable;
        cout << "\n";

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

        cout << "Exponent of newly generated or old variable: " << exponentToBe;
        cout << "\n";

        carl::Monomial::Arg newMonomial = carl::createMonomial(newlyGeneratedOrOldVariable, (carl::exponent)exponentToBe);

        cout << "new Monomial: " << newMonomial;
        cout << "\n";
        cout << "\n";

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

            carl::Monomial::Arg createdMonomial = carl::createMonomial(std::initializer_list<std::pair<carl::Variable, carl::exponent>>
           (
                   {std::make_pair(first,(carl::exponent)1), std::make_pair(second, (carl::exponent)1)}
           ),
           (carl::exponent)(1));

            //carl::Variable GeneratedVariable = createZVariable();
            carl::Variable newlyGeneratedOrOldVariable = insertIntoMapOrRetrieveExistingVariable(createdMonomial);
            //insertIntoMap(GeneratedVariable, createdMonomial);

            variables.push_front(newlyGeneratedOrOldVariable);

        }

        return variables.front();
    }

    std::list<carl::Variable> extraVariablesForOddExponenet;

    /**
     * Replace square of variable (x_0^2) of a monomial (x_0^7) by a variable (z_0),
     * create a linear monomial (z_1)
     * and insert the variable as key with monomial as value in the map
     * @param Variable a carl::Variable object
     * @param exponent an odd exponent
     * @return new linear monomial
     */
    carl::Monomial::Arg monomialForOddExponent(carl::Variable Variable, int exponent){
        int exponentToBe = divisionOfExponentByTwo(exponent);
        //carl::Variable GeneratedVariable = createZVariable();
        carl::Monomial::Arg monomialAsSquareOfVariable = createSquareOfVariable(Variable);

        //insertIntoMap(GeneratedVariable, monomialAsSquareOfVariable);
        carl::Variable newlyGeneratedOrOldVariable = insertIntoMapOrRetrieveExistingVariable(monomialAsSquareOfVariable);

        cout << "Exponent of newly generated or old variable: " << exponentToBe;
        cout << "\n";

        carl::Monomial::Arg newMonomial = carl::createMonomial(newlyGeneratedOrOldVariable, (carl::exponent)exponentToBe);

        extraVariablesForOddExponenet.push_front(Variable);

        // get linear monomial
        while (!newMonomial->isLinear()) {

            if(newMonomial->begin()->second % 2 == 0){

                newMonomial = monomialForEvenExponent(newMonomial->begin()->first, newMonomial->begin()->second);

            } else {
                newMonomial = monomialForOddExponent(newMonomial->begin()->first, newMonomial->begin()->second);
            }
        }

        // create newMonomial by multiplying newMonomial with the list extraVariablesForOddExponenet
        if(newMonomial->isLinear()) {
            extraVariablesForOddExponenet.push_front(newMonomial->begin()->first);
            newMonomial = carl::createMonomial((createLinearVariable(extraVariablesForOddExponenet)), (carl::exponent)1);
        }

        cout << "new Monomial: " << newMonomial;
        cout << "\n";
        cout << "\n";

        return newMonomial;
    }

    /**
     * create monomial which is linear
     * @param Variable a carl Variable object
     * @param exponent even or odd exponent of the variable
     * @return a linear monomial
     */
    carl::Monomial::Arg createMonomialOfLinearVariable(carl::Variable Variable, int exponent)
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

            cout << "final Linear Monomial: " << monomial << " tDeg: " << monomial->tdeg();
            cout << "\n";

            return monomial;
        }


        return createMonomialOfLinearVariable(monomial->begin()->first, monomial->begin()->second);
    }

    /**
     * It linearizes a non-linear monomial
     * @param monomial a monomoal object
     * @return a linear variable
     */
    carl::Variable linearization(carl::Monomial::Arg monomial){

        std::list<carl::Variable> variables;

        carl::Variable finalVariable;

        for (auto it = monomial->begin(); it != monomial->end(); ++it) {

                carl::Monomial::Arg monomial = createMonomialOfLinearVariable(it->first, it->second);

                cout << "Received final Monomial is: " << monomial;
                cout << "\n";
                cout << "\n";

                variables.push_back(monomial->begin()->first);
            }

            finalVariable = createLinearVariable(variables);

        return  finalVariable;
    }


    template<class Settings>
    bool AbstractModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        FormulaT formula = _subformula->formula();

        //get constraint
        const ConstraintT& constraint = _subformula->formula().constraint();

        cout << "\n";
        cout << "Constraint is: " << constraint;
        cout << "\n";
        cout << "\n";

        //get polynomial(lhs) of constraint
        carl::MultivariatePolynomial<Rational> poly = constraint.lhs();
        //counter of op[]
        int indexCount = 0;

        //size of array
        carl::MultivariatePolynomial<Rational> op[poly.getTerms().size()];
        int n = sizeof(op) / sizeof(op[0]);

        // loops over each term and create linear polynomials
        for( auto& term : poly.getTerms() ) {

           if (!term.isConstant() && term.isLinear()) { //if the term is already linear and not a constant

                carl::MultivariatePolynomial<Rational> p(term);
                op[indexCount] = p;

                cout << "Monomial is: " << term.monomial() << " (alreday linear)";
                cout << "\n";
                cout << "\n";

            }else if (!term.isConstant()) { //if the term is a product of two or more variables

                //get monomial
                carl::Monomial::Arg monomial = term.monomial();
                cout << "Monomial is: " << monomial;
                cout << "\n";

                //get the linearized variable of the monomial
                carl::Variable finalVariable = linearization(monomial);

                //create new polynomial
                carl::MultivariatePolynomial<Rational> p(term.coeff()*finalVariable);

                cout << "Generated MultiVariantPolynomial: " << p;
                cout << "\n";
                cout << "\n";

                op[indexCount] = p;

            } else { //if the term is a constants

                //create new polynomial
                carl::MultivariatePolynomial<Rational> p(term);
                op[indexCount] = p;

            }

            indexCount++;
        }

        //convert op of array type to vector
        std::vector<carl::MultivariatePolynomial<Rational>> operands(op, op + n);
        cout << "Vector: " << operands;
        cout << "\n";

        //construction lhs of the constraint
        carl::MultivariatePolynomial<Rational> finalPoly(Poly::ConstructorOperation::ADD,operands);

        //create new formula
        FormulaT  finalFormula = FormulaT(finalPoly, constraint.relation());
        cout << "Generated final Formula: " << finalFormula;
        cout << "\n";
        cout << "Generated New constraint: " << finalFormula.constraint();
        cout << "\n";
        cout << "\n";

        return true; // This should be adapted according to your implementation.
    }

    template<class Settings>
    void AbstractModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
        // Your code.
    }

    template<class Settings>
    void AbstractModule<Settings>::updateModel() const
    {
        mModel.clear();
        if( solverState() == Answer::SAT )
        {
            // Your code.
        }
    }

    template<class Settings>
    Answer AbstractModule<Settings>::checkCore()
    {
        // Your code.
        return Answer::UNKNOWN; // This should be adapted according to your implementation.
    }

}

#include "Instantiation.h"
