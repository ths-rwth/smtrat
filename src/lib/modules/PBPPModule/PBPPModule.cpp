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
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void PBPPModule<Settings>::init()
	{}
	
	template<class Settings>
	bool PBPPModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		std::cout << "ADDCORE" << std::endl;
		std::cout << _subformula->formula() << std::endl;
		if (objective() != carl::Variable::NO_VARIABLE) {
			for (auto var: objectiveFunction().gatherVariables()) {
				mVariablesCache.emplace(carl::Variable(var.getId(), carl::VariableType::VT_BOOL), var);
			}
		}
		FormulaT formula = mVisitor.visitResult(_subformula->formula(), checkFormulaTypeFunction);
		addSubformulaToPassedFormula(formula, _subformula->formula());
		return true;
	}
	
	template<class Settings>
	void PBPPModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{	
		// Your code.
	}
	
	template<class Settings>
	void PBPPModule<Settings>::updateModel() const
	{
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
		std::cout << "CHECKFORMULATYPE" << std::endl;
		if(formula.getType() != carl::FormulaType::PBCONSTRAINT){
			return formula;
		} 
		const carl::PBConstraint& c = formula.pbConstraint();
		carl::Relation cRel  = c.getRelation();
		const auto& cLHS	 = c.getLHS();
		bool positive = true;
		bool negative = true;
		int cRHS = c.getRHS();
		int sum  = 0;

		for(auto it = cLHS.begin(); it != cLHS.end(); it++){
			sum += it->first;
			if(it->first < 0){
				positive = false;
			}else if(it->first > 0){
				negative = false;
			}
		}
		if(cLHS.size() == 1 ||
			(cLHS.size() < 4 
					&& !(positive && cRHS > 0 && sum > cRHS 
					&& (cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER || cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS))
						&&  !(negative && cRHS < 0 && (cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER) && sum < cRHS && cLHS.size() > 1)
							&& !(negative && cRHS < 0 && (cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS) && sum < cRHS)
								&& !((positive || negative) && cRel == carl::Relation::NEQ && sum != cRHS && cRHS != 0)
									&& !((positive || negative) && cRel == carl::Relation::NEQ && sum == cRHS && cRHS != 0)
			)){
			auto res = forwardAsBoolean(formula);
			SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
			return res;
			}
		auto res = forwardAsArithmetic(formula);
		SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
		return res;
		
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::convertSmallFormulaToBoolean(const FormulaT& formula){
		std::cout << "CONVERTSMALLFORMULA" << std::endl;
		const carl::PBConstraint& c  = formula.pbConstraint();
		carl::Relation cRel   = c.getRelation();
		const auto& cLHS      = c.getLHS();
		int lhsCoeff    = cLHS.begin()->first;
		FormulaT lhsVar = FormulaT(cLHS.begin()->second);
		int cRHS 		= c.getRHS();

		if(cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER){
			if(lhsCoeff > 0){
				if(cRHS < lhsCoeff && cRHS < 0){
					//5 x1 >= -3 or 5 x1 > -3 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else if(cRHS < lhsCoeff && cRHS > 0){
					//5 x1 >= 3 or 5 x1 > 3 ===> x1
					return FormulaT(lhsVar);
				}else if(cRHS == 0 && cRel == carl::Relation::GEQ){
					//5 x1 >= 0 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else if(cRHS == 0 && cRel == carl::Relation::GREATER){
					//5 x1 > 0 ===> x1
					return FormulaT(lhsVar);
				}else if(cRHS > lhsCoeff){
					//10 x1 >= 12 or 10 x1 > 12 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
 				}else if(cRHS == lhsCoeff && cRel == carl::Relation::GEQ){
 					//10 x1 >= 10 ===> x1
 					return FormulaT(lhsVar);
				}else if(cRHS == lhsCoeff && cRel == carl::Relation::GREATER){
					//10 x1 > 10 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}
			}else if(lhsCoeff < 0){
				if(cRHS < lhsCoeff){
					//-10 x1 >= -20 or -10 x1 > -20 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else if(cRHS == 0 && cRel == carl::Relation::GEQ){
					//-2 x1 >= 0 ===> not x1
					return FormulaT(lhsVar.negated());
				}else if(cRHS == 0 && cRel == carl::Relation::GREATER){
					//-3 x1 > 0 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}else if(cRHS > 0){
					//-2 x1 >= 10 or -2 x1 > 10 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}else if(cRHS > lhsCoeff && cRHS < 0){
					//-20 x1 >= -3 or -20 x1 > -3 ===> not x1
					return FormulaT(lhsVar.negated());
				}else if(cRHS > lhsCoeff && cRHS > 0){
					//-20 x1 >= 3 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
 				}else if(cRHS == lhsCoeff && cRel == carl::Relation::GEQ){
 					//-20 x1 >= -20 ===> TRUE
 					return FormulaT(carl::FormulaType::TRUE);
				}else if(cRHS == lhsCoeff && cRel == carl::Relation::GREATER){
					//-20 x1 > -20 ===> not x1
					return FormulaT(lhsVar.negated());
				}
			}
		}else if(cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS){
			if(lhsCoeff > 0){
				if(cRHS < lhsCoeff && cRHS > 0){
					//10 x1 <= 3 or 10 x1 < 3 ===>  not x1
					return FormulaT(lhsVar.negated());
				}else if(cRHS < lhsCoeff && cRHS < 0){
					//10 x1 <= -2 or 10 x1 < -2 ===> FALSE 
					return FormulaT(carl::FormulaType::FALSE);
				}else if(cRHS == 0 && cRel == carl::Relation::LEQ){
					//10 x1 <= 0 ===> not x1
					return FormulaT(lhsVar.negated());
				}else if(cRHS == 0 && cRel == carl::Relation::LESS){
					//10 x1 < 0 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE); 
				}else if(cRHS > lhsCoeff){
					//6 x1 <= 39 or 3 x1 < 23 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
 				}else if(cRHS == lhsCoeff && cRel == carl::Relation::LEQ){
 					//3 x1 <= 3 ===> TRUE
 					return FormulaT(carl::FormulaType::TRUE);
				}else if(cRHS == lhsCoeff && cRel == carl::Relation::LESS){
					//3 x1 < 3 ===> not x1
					return FormulaT(lhsVar.negated());
				}
			}else if(lhsCoeff < 0){
				if(cRHS < lhsCoeff){
					//-3 x1 <= -43 or -3 x1 < -43 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}else if(cRHS == 0 && cRel == carl::Relation::LEQ){
					//-3 x1 <= 0 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else if(cRHS == 0 && cRel == carl::Relation::LESS){
					//-3 x1 < 0 ===> x1
					return FormulaT(lhsVar);
				}else if(cRHS > 0){
					//-3 x1 <= 5 or -3 x1 < 5 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else if(cRHS > lhsCoeff && cRHS < 0){
					//-30 x1 <= -5 or -30 x1 < -5 ===> x1
					return FormulaT(lhsVar);
				}else if(cRHS > lhsCoeff && cRHS > 0){
					//-30 x1 <= 5 or -30 x1 < 5 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
 				}else if(cRHS == lhsCoeff && cRel == carl::Relation::LEQ){
 					//-20 x1 <= -20 ===> x1
 					return FormulaT(lhsVar);
				}else if(cRHS == lhsCoeff && cRel == carl::Relation::LESS){
					//-20 x1 < -20 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}
			}
		}else if(cRel == carl::Relation::EQ){
			if(lhsCoeff == cRHS){
				//-2 x1 = -2 or 3 x1 = 3 ===> x1
				return FormulaT(lhsVar);
			}else if(cRHS == 0){
				//2 x1 = 0 or -3 x1 = 0 ===> not x1
				return FormulaT(lhsVar.negated());
			}else{
				//2 x1 = 4 ===> FALSE
				return FormulaT(carl::FormulaType::FALSE);
			}
		}else if(cRel == carl::Relation::NEQ){
			if(lhsCoeff == cRHS){
				//3 x1 != 3 ===> not x1
				return FormulaT(lhsVar.negated());
			}else if(cRHS == 0){
				//3 x1 != 0 ===> x1
				return FormulaT(lhsVar);
			}else if(lhsCoeff != cRHS){
				//3 x1 != 5 ===> TRUE
				return FormulaT(carl::FormulaType::TRUE);
			}
		}
		return formula;
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::convertBigFormulaToBoolean(const FormulaT& formula){
		std::cout << "CONVERTBIGFORMULA" << std::endl;
		const carl::PBConstraint& c = formula.pbConstraint();
		const auto& cLHS 	 = c.getLHS();
		carl::Relation cRel  = c.getRelation();
		auto cVars	  = c.gatherVariables();
		int cRHS 	  = c.getRHS();
		bool positive = true;
		bool negative = true;
		int sum = 0;

		for(auto it = cLHS.begin(); it != cLHS.end(); it++){
			if(it->first < 0){
				positive = false;
			}else if(it->first > 0){
				negative = false;
			}
			sum += it->first;
		}

		if(!positive && !negative && cRHS >= 0 && cRel == carl::Relation::GEQ && sum >= cRHS){
			return convertNormalizedFormula(formula);
		}else if(!positive && !negative){
			return forwardAsArithmetic(formula);
		}

		if(positive && (cRel == carl::Relation::GREATER || cRel == carl::Relation::GEQ)){
			if(cRHS < 0){
				//5 x1 + 2 x2 + 3 x3 >= -5 or 5 x1 + 2 x2 + 3 x3 > -5 
				//===> false -> x1 AND x2 AND x3 ===> TRUE
				return FormulaT(carl::FormulaType::TRUE);
			}else if(cRHS == 0){
				if(cRel == carl::Relation::GEQ){
					// 5 x1 + 2 x2 + 3 x3 >= 0 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}
				// 5 x1 + 2 x2 + 3 x3 > 0 ===> x1 or x2 or x3
				return generateVarChain(cVars, carl::FormulaType::OR);
			}else{
				//RHS > 0
				if(sum < cRHS){
					//5 x1 + 2 x2 + 3 x3 >= 20 or 5 x1 + 2 x2 + 3 x3 > 20 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}else if(sum == cRHS && cRel == carl::Relation::GEQ){
					//5 x1 + 2 x2 + 3 x3 >= 10 ===> x1 and x2 and x3
					return generateVarChain(cVars, carl::FormulaType::AND);
				}else if(sum == cRHS && cRel == carl::Relation::GREATER){
					//5 x1 + 2 x2 + 3 x3 > 10 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}
			}
		}else if(negative && (cRel == carl::Relation::GREATER || cRel == carl::Relation::GEQ)){
			if(cRHS > 0){
				//-5 x1 - 2 x2 - 3 x3 >= 5 or -5 x1 - 2 x2 - 3 x3 > 5 ===> FALSE
				return FormulaT(carl::FormulaType::FALSE);
			}else if(cRHS == 0){
				if(cRel == carl::Relation::GEQ){
					//-5 x1 - 2 x2 - 3 x3 >= 0 ===> (x1 or x2 or x3) -> false
					FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::OR);
					FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
					return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
				}else if(cRel == carl::Relation::GREATER){
					//-5 x1 - 2 x2 - 3 x3 > 0 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}
			}else if(cRHS < 0){
				if(sum == cRHS && cRel == carl::Relation::GEQ){
					//-5 x1 - 2 x2 - 3 x3 >= -10  ===> false -> x1 and x2 and x3 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else if(sum == cRHS && cRel == carl::Relation::GREATER){
					//-5 x1 - 2 x2 - 3 x3 > -10  ===> x1 and x2 and x3 -> false
					FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::AND);
					FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
					return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
				}else if(sum > cRHS){
					//-3 x1 -3 x2 -1 x3 >= -20 or -3 x1 -3 x2 -1 x3 > -20 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}
			}
		}else if(positive && (cRel == carl::Relation::LESS || cRel == carl::Relation::LEQ)){
			if(cRHS < 0){
				//5 x1 +2 x2 +3 x3 <= -5 or 5 x1 +2 x2 +3 x3 < -5 ===> FALSE
				return FormulaT(carl::FormulaType::FALSE);
			}else if(cRHS == 0){
				if(cRel == carl::Relation::LEQ){
					//5 x1 +2 x2 +3 x3 <= 0 ===> (x1 or x2 or x3) -> false
					FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::OR);
					FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
					return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
				}else if(cRel == carl::Relation::LESS){
					//5 x1 +2 x2 +3 x3 < 0 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);	
				}
			}else if(cRHS > 0){
				if(sum == cRHS && cRel == carl::Relation::LEQ){
					//5 x1 +2 x2 +3 x3 <= 10 ===> false -> x1 and x2 and x3 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else if(sum == cRHS && cRel == carl::Relation::LESS){
					//5 x1 +2 x2 +3 x3 < 10 ===> x1 and x2 and x3 -> false
					FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::AND);
					FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
					return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
				}else if(sum < cRHS){
					//5 x1 +2 x2 +3 x3 <= 20 or 5 x1 +2 x2 +3 x3 < 20 ===> false -> x1 and x2 and x3 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}
			}
		}else if(negative && (cRel == carl::Relation::LESS || cRel == carl::Relation::LEQ)){
			if(cRHS > 0){
				//-5 x1 -2 x2 -3 x3 <= 5 or -5 x1 -2 x2 -3 x3 < 5 ===> false -> x1 and x2 and x3 ===> TRUE
				return FormulaT(carl::FormulaType::TRUE);
			}else if(cRHS == 0){
				if(cRel == carl::Relation::LEQ){
					//-5 x1 -2 x2 -3 x3 <= 0 ===> false -> x1 and x2 and x3 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else if(cRel == carl::Relation::LESS){
					//-5 x1 -2 x2 -3 x3 < 0 ===> true -> x1 or x2 or x3
					FormulaT subformulaA = FormulaT(carl::FormulaType::TRUE);
					FormulaT subformulaB = generateVarChain(cVars, carl::FormulaType::OR);
					return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
				}
			}else if(cRHS < 0){
				if(sum > cRHS){
					//-5 x1 -2 x2 -3 x3 < -15 or -5 x1 -2 x2 -3 x3 <= -15 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}else if(sum == cRHS && cRel == carl::Relation::LEQ){
					//-5 x1 -2 x2 -3 x3 <= -10 ===> x1 and x2 and x3 -> false
					FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::AND);
					FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
					return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
				}else if(sum == cRHS && cRel == carl::Relation::LESS){
					//-5 x1 -2 x2 -3 x3 < -10 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}
			}
		}else if(cRel == carl::Relation::EQ){
			if(sum != cRHS && cRHS != 0){
				//5 x1 +2 x2 +3 x3 = 5 ===> FALSE
				return FormulaT(carl::FormulaType::FALSE);
			}else if(sum != cRHS && cRHS == 0){
				//5 x1 +2 x2 +3 x3 = 0 ===> (x1 or x2 or x3 -> false)
				FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::OR);
				FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
				return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);				
			}
			//5 x1 +2 x2 +3 x3 = 10 ===> x1 and x2 and x3
			return generateVarChain(cVars, carl::FormulaType::AND);
		}else if(cRel == carl::Relation::NEQ){
			if(sum != cRHS && cRHS == 0){
				//5 x1 +2 x2 +3 x3 = 0 ===> x1 and x2 and x3 
				return generateVarChain(cVars, carl::FormulaType::AND);
			}	
		}
	return formula;
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::convertNormalizedFormula(const FormulaT& formula){
		std::cout << "CONVERTTOPOSITIVEFORMULA" << std::endl;
		const carl::PBConstraint& c = formula.pbConstraint();
		const auto& cLHS = c.getLHS();
		FormulasT newSubformulas;

		//-1 x1 +1 x2 -1 x3 >= 0 ===> +1 not(x1) +1 x2 +1 not(x3) >= 0 ===> not(x1) or x2 or not(x3) ===> x1 and not(x2) and x3
		for(auto it : cLHS){
			FormulaT f = FormulaT(it.second);
			if(it.first > 0){
				newSubformulas.push_back(f.negated());
			}
		}
		return FormulaT(carl::FormulaType::AND, std::move(newSubformulas));
		
	} 

	template<typename Settings>
	FormulaT PBPPModule<Settings>::forwardAsBoolean(const FormulaT& formula){
		std::cout << "FORWARDASBOOLEAN" << std::endl;
		const carl::PBConstraint& c = formula.pbConstraint();
		const auto& cLHS 	 = c.getLHS();

		if(cLHS.size() == 1){
			return convertSmallFormulaToBoolean(formula);
		}else if(cLHS.size() < 4){
			return convertBigFormulaToBoolean(formula);
		}
	 	return formula;
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::generateVarChain(const std::vector<carl::Variable>& vars, carl::FormulaType type){
		std::cout << "GENERATEVARCHAIN" << std::endl;
		FormulasT newSubformulas;
		for(auto var: vars){
			FormulaT newFormula = FormulaT(var);
			newSubformulas.push_back(newFormula);
		}
		return FormulaT(type, std::move(newSubformulas));
	}

	/*
	/ Converts PBConstraint into a LRA formula.
	*/
	template<typename Settings>
	FormulaT PBPPModule<Settings>::forwardAsArithmetic(const FormulaT& formula){
		std::cout << "FORWARDASARITHMETIC" << std::endl;
		carl::Variables variables;
		formula.allVars(variables);
		std::vector<carl::Variable> currentVars;
		std::map<carl::Variable, carl::Variable> currentVarsMap;
		for(auto it = variables.begin(); it != variables.end(); it++){
			auto finderIt = mVariablesCache.find(*it);
			if(finderIt == mVariablesCache.end()){
				mVariablesCache.insert(std::pair<carl::Variable, carl::Variable>(*it, carl::freshVariable(carl::VariableType::VT_INT)));
			}
		}
		Poly lhs;
		const carl::PBConstraint& c = formula.pbConstraint();
		const auto& cLHS = c.getLHS();
		for(auto it = cLHS.begin(); it != cLHS.end(); it++){
			auto finder = mVariablesCache.find(it->second);	
			carl::Variable curVariable = finder->first; 
			Poly pol(curVariable);
			lhs =  lhs + Rational(it->first) * pol;
		}
		lhs = lhs - Rational(c.getRHS());
		FormulaT subformulaA = FormulaT(lhs, c.getRelation());

		//Adding auxiliary constraint to ensure variables are assigned to 1 or 0.
		FormulaT subformulaB = createAuxiliaryConstraint(formula);
		FormulaT subformulaC = FormulaT(carl::FormulaType::AND, subformulaA, subformulaB);

		//Adding auxiliary constraint to interconnect the bool and int variables
		FormulaT subformulaD = interconnectVariables(formula);

		return FormulaT(carl::FormulaType::AND, subformulaC, subformulaD);
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::createAuxiliaryConstraint(const FormulaT& formula){
		std::cout << "CREATEAUXILIARYCONSTRAINT" << std::endl;
		const carl::PBConstraint& c = formula.pbConstraint();
		auto boolVars        = c.gatherVariables();
		std::vector<carl::Variable> intVars;
		for(auto var : boolVars){
			if(std::find(mCheckedVars.begin(), mCheckedVars.end(), var) != mCheckedVars.end()){
				//There are no auxiliary constraints for this variable
				intVars.push_back(mVariablesCache.find(var)->second);
				mCheckedVars.push_back(var);
			}
		}

		FormulasT newSubformulas;
		for(auto var : intVars){
			Poly intVar(var);
			FormulaT subformulaA = FormulaT(intVar, carl::Relation::EQ);
			FormulaT subformulaB = FormulaT(intVar - Rational(1), carl::Relation::EQ);
			FormulaT newFormula = FormulaT(carl::FormulaType::XOR, subformulaA, subformulaB);
			newSubformulas.push_back(newFormula);
		}
		return FormulaT(carl::FormulaType::AND, std::move(newSubformulas));
	}

		template<typename Settings>
	FormulaT PBPPModule<Settings>::interconnectVariables(const FormulaT& formula){
		std::cout << "INTERCONNECTVARIABLES" << std::endl;
		const carl::PBConstraint& c = formula.pbConstraint();
		auto boolVars 		 = c.gatherVariables();
		std::map<carl::Variable, carl::Variable> varsMap;
		for(auto var : boolVars){
			if(std::find(mInterconectedVars.begin(), mInterconectedVars.end(), var) != mInterconectedVars.end()){
				//The variable has to be interconected
				varsMap.insert(*mVariablesCache.find(var));
				mInterconectedVars.push_back(var);
			}
			//The variable is already interconected
		}

		FormulasT newSubformulas;
		for(auto var : varsMap){
			FormulaT boolVar = FormulaT(var.first);
			Poly intVar(var.second);
			FormulaT subformulaA = FormulaT(intVar - Rational(1), carl::Relation::EQ);
			FormulaT subformulaB = FormulaT(carl::FormulaType::IMPLIES, boolVar, subformulaA);
			FormulaT subformulaC = FormulaT(intVar, carl::Relation::EQ);
			FormulaT subformulaD = FormulaT(carl::FormulaType::IMPLIES, boolVar.negated(), subformulaC);
			FormulaT newFormula  = FormulaT(carl::FormulaType::OR, subformulaB, subformulaD);
			newSubformulas.push_back(newFormula);
		}
		return FormulaT(carl::FormulaType::AND, std::move(newSubformulas));

	}

}

#include "Instantiation.h"
