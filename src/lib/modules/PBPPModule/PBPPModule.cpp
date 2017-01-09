/**
 * @file PBPP.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2016-11-23
 * Created on 2016-11-23.
 */

#include "PBPPModule.h"

namespace smtrat
{

	template<class Settings>
	PBPPModule<Settings>::PBPPModule(const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager )
#ifdef SMTRAT_DEVOPTION_Statistics
		, mStatistics(Settings::moduleName)
#endif
	{
		checkFormulaTypeFunction = std::bind(&PBPPModule<Settings>::checkFormulaType, this, std::placeholders::_1);

	}
	
	template<class Settings>
	PBPPModule<Settings>::~PBPPModule()
	{}
	
	template<class Settings>
	bool PBPPModule<Settings>::informCore( const FormulaT& _constraint )
	{
		// Your code.
		std::cout << "INFORMCORE" << std::endl;
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void PBPPModule<Settings>::init()
	{}
	
	template<class Settings>
	bool PBPPModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		std::cout << "ADDCORE" << std::endl;
		std::cout << "Formel: ";
		std::cout << _subformula->formula() << std::endl;
		FormulaT formula = mVisitor.visitResult(_subformula->formula(), checkFormulaTypeFunction);
		addSubformulaToPassedFormula(formula, _subformula->formula());
		return true;
	}
	
	template<class Settings>
	void PBPPModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		std::cout << "REMOVECORE" << std::endl;		
		// Your code.
	}
	
	template<class Settings>
	void PBPPModule<Settings>::updateModel() const
	{
		std::cout << "UPDATEMODEL" << std::endl;
		mModel.clear();
		if( solverState() == Answer::SAT )
		{
			getBackendsModel();
		}
	}
	
	template<class Settings>
	Answer PBPPModule<Settings>::checkCore()
	{
		std::cout << "CHECKCORE" << std::endl;
		Answer ans = runBackends();
		if (ans == UNSAT) {
			generateTrivialInfeasibleSubset();
		}
		return ans;
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::checkFormulaType(const FormulaT& formula){
		std::cout << "CHECKFORMULATYPE: ";
		if(formula.getType() != carl::FormulaType::PBCONSTRAINT){
			std::cout << formula;
			std::cout << " - Kein pbConstraint" << std::endl;
			return formula;
		} 
		carl::PBConstraint c = formula.pbConstraint();
		if(c.getLHS().size() < 4){
							std::cout << "boolean" << std::endl;
			return forwardAsBoolean(formula);
		}
						std::cout << "arithmetic" << std::endl;
		return forwardAsArithmetic(formula);
	}


	/*
	/ Convert PBConstraint into a boolean formula.
	*/
	template<typename Settings>
	FormulaT PBPPModule<Settings>::forwardAsBoolean(const FormulaT& formula){
		std::cout << "FORWARDASBOOLEAN" << std::endl;
		carl::PBConstraint c = formula.pbConstraint();
		std::vector<std::pair<carl::Variable, int>> cLHS = c.getLHS();
		carl::Relation cRel = c.getRelation();
		int cRHS = c.getRHS();
		if(c.isTrue()){
			//All coefficients on the lhs are >= 0, the rhs is <= 0 and the relation is GEQ
			FormulaT f = FormulaT(carl::FormulaType::TRUE);
			SMTRAT_LOG_INFO("smtrat.pbc", formula << " is true.");
			return f;
		}else if(c.isFalse()){
			//All coefficients on the lhs are <= 1, the rhs is > 0 and the relation is GEQ
			FormulaT f = FormulaT(carl::FormulaType::FALSE);
			SMTRAT_LOG_INFO("smtrat.pbc", formula << " is false.");
			return f;
		}else if(cLHS.size() == 1 && cRel == carl::Relation::GEQ){
				if(cLHS.begin()->second == cRHS && cRHS < 0){
					// -k x1 >= -k  => false -> x1
					FormulaT subformulaA = FormulaT(carl::FormulaType::FALSE);
					FormulaT subformulaB = FormulaT(cLHS.begin()->first);
					FormulaT f = FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
					SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << f);
					return f;
				}else if(cLHS.begin()->second < 0 && cRHS == 0){
					// -k x1 >= 0 => x1 -> false
					FormulaT subformulaA = FormulaT(cLHS.begin()->first);
					FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
					FormulaT f = FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
					SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << f);
					return f;
				}else if(cLHS.begin()->second == cRHS && cRHS > 0){
					// k x1 >= k => true -> x1
					FormulaT subformulaA = FormulaT(carl::FormulaType::TRUE);
					FormulaT subformulaB = FormulaT(cLHS.begin()->first);
					FormulaT f = FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
					SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << f);
					return f;
				}
		}
			
	
		SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << formula);
		return formula;
	}

	/*
	/ Convert PBConstraint into a LRA formula.
	*/
	template<typename Settings>
	FormulaT PBPPModule<Settings>::forwardAsArithmetic(const FormulaT& formula){
		std::cout << "FORWARDASARITHMETIC" << std::endl;
		carl::Variables variables;
		formula.allVars(variables);
		for(auto it = variables.begin(); it != variables.end(); it++){
			auto finderIt = mVariablesCache.find(*it);
			if(finderIt == mVariablesCache.end()){
				mVariablesCache.insert(std::pair<carl::Variable, carl::Variable>(*it, carl::freshVariable(carl::VariableType::VT_INT)));
			}
		}
		Poly lhs;
		carl::PBConstraint c = formula.pbConstraint();
		std::vector<std::pair<carl::Variable, int>> cLHS = c.getLHS();
		for(auto it = cLHS.begin(); it != cLHS.end(); it++){
			auto finder = mVariablesCache.find(it->first);	
			carl::Variable curVariable = finder->second; 
			Poly pol(curVariable);
			lhs =  lhs + Rational(it->second) * pol;
		}
		lhs = lhs - Rational(c.getRHS());
		FormulaT f = FormulaT(lhs, c.getRelation());
		SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << f);
        return f;
	}

}

#include "Instantiation.h"
