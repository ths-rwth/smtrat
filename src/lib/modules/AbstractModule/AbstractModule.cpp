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
		Module( _formula, _conditionals, _manager ),
        mLRAFormula( new ModuleInput()),
        mNRAFormula( new ModuleInput())
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



	template<class Settings>
	bool AbstractModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		// Your code.
        const ConstraintT& constraint = _subformula->formula().constraint();
        cout << "\n";
        cout << "Constraint is: " << constraint;
        cout << "\n";
        cout << "\n";

        carl::MultivariatePolynomial<Rational> poly = constraint.lhs();
        //counter of op[]
        int indexCount = 0;

        //size of array
        carl::MultivariatePolynomial<Rational> op[poly.getTerms().size()];
        int n = sizeof(op) / sizeof(op[0]);
        std::string VariableName = "z_";



        for( auto& term : poly.getTerms() )
        {
            if( !term.isConstant() )
            {
                //monomials
                cout << "Monomial is: " << term.monomial();
                cout << "\n";

                //create new variables
                std::string GeneratedVariableName = VariableName + std::to_string(variableCount);
                carl::Variable GeneratedVariable = carl::freshRealVariable(GeneratedVariableName);
                cout << "GeneratedVariableName: " << GeneratedVariable;
                cout << "\n";


                //create new polynomial
                carl::MultivariatePolynomial<Rational> p(term.coeff()*GeneratedVariable);
                cout << "Generated MultiVariantPolynomial: " << p;
                cout << "\n";
                cout << "\n";
                op[indexCount] = p;

                // inserting the monomial to the map
                carl::Monomial::Arg mMonomial = term.monomial();
                smtrat::MonomialMappingByVariablePool::getInstance().InsertMonomialMapping(GeneratedVariable, mMonomial);
                carl::Monomial::Arg mFoundMonomial  = smtrat::MonomialMappingByVariablePool::getInstance().Monomial(GeneratedVariable);
                cout << "instance of monomial: " << mFoundMonomial;
                cout << "\n";
                cout << "\n";

                variableCount++;
            } else {
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
        cout << "\n";

        //construction lhs of the constraint
        carl::MultivariatePolynomial<Rational> finalPoly(Poly::ConstructorOperation::ADD,operands);
        //create new formula
        FormulaT  finalFormula = FormulaT(finalPoly, constraint.relation());
        cout << "Generated Formula: " << finalFormula;
        cout << "\n";
        cout << "Generated New constraint: " << finalFormula.constraint();
        cout << "\n";

        cout << "\n";

        ////////////////////////////////////////////////
        //
        // Adding the Linearized Formula to the global
        // ModuleInput type variable. This global
        // variable will be used to add all of the
        // Linearized formulas to the passed formula
        //
        ////////////////////////////////////////////////
        mLRAFormula->add(finalFormula, false);
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
		////////////////////////////////////////////////
		//
		// Adding the Linearized Formula to the passed
		// Formula
		//
		////////////////////////////////////////////////
        for (auto it = mLRAFormula->begin(); it != mLRAFormula->end(); ++it) {
            addReceivedSubformulaToPassedFormula(it);
        }
        auto ans = runBackends();

        ////////////////////////////////////////////////
        //
        // we only find NRA solution iff
        // the linearized formula satisfies
        //
        ////////////////////////////////////////////////
        if (ans != UNSAT) {
            Model bmodel = backendsModel();
            cout << "Solution: " << bmodel;
            cout << "\n";

            for (auto const& item : bmodel) {
                ModelVariable modelVariable = item.first;
                ModelValue  modelValue = item.second;
                carl::Monomial::Arg mFoundMonomial  = smtrat::MonomialMappingByVariablePool::getInstance().Monomial(modelVariable.asVariable());
                cout << "Found monomial: " << mFoundMonomial;
                cout << "\n";
                cout << "Found double: " << modelValue.asRational();
                TermT term = TermT(modelValue.asRational());
                cout << "created Term of the constant: " << term;
                carl::MultivariatePolynomial<Rational> pValue(term);
                cout << "\n";

                carl::MultivariatePolynomial<Rational> p(mFoundMonomial);
                cout << "Created Polynomial: " << p;
                cout << "\n";

                std::vector<carl::MultivariatePolynomial<Rational>> operands = {p , pValue};

                cout << "operands: " << operands;
                cout << "\n";

                carl::MultivariatePolynomial<Rational> finalPoly(Poly::ConstructorOperation::SUB,operands);


                FormulaT  createdFormula = FormulaT(finalPoly, carl::Relation::EQ);
                cout << "Created Formula: " << createdFormula;
                cout << "\n";
                mNRAFormula->add(createdFormula, false);

            }

            for (auto it = mNRAFormula->begin(); it != mNRAFormula->end(); ++it) {
                cout << "Adding Formula: " << it->formula();
                cout << "\n";
                addReceivedSubformulaToPassedFormula(it);
            }

            ans = runBackends();

            cout << "The formula is: " << ans;
            cout << "\n";
        }
		return ans; // This should be adapted according to your implementation.
	}
}

#include "Instantiation.h"
