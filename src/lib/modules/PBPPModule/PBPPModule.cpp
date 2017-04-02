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
		Answer ans = runBackends();
		if (ans == UNSAT) {
			generateTrivialInfeasibleSubset();
		}
		return ans;
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::checkFormulaType(const FormulaT& formula){
		std::cout << "CHECKCORE" << std::endl;
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

		if(cLHS.size() == 1){
			std::cout << "Convert small formula..." << std::endl;
			auto res = convertSmallFormula(formula);
			SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
			std::cout << "OK" << std::endl;
			return res;
		}else if(!(positive && cRHS > 0 && sum > cRHS 
					&& (cRel == carl::Relation::GREATER || cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS))
						&&  !(negative && cRHS < 0 && (cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER) && sum < cRHS && cLHS.size() > 1)
							&& !(negative && cRHS < 0 && (cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS) && sum < cRHS)
								&& !((positive || negative) && cRel == carl::Relation::NEQ && sum != cRHS && cRHS != 0)
									&& !((positive || negative) && cRel == carl::Relation::NEQ && sum == cRHS && cRHS != 0)
										&& ((!positive && !negative && (cRel == carl::Relation::GEQ || cRel == carl::Relation::LEQ) && sum >= cRHS) || positive || negative)	
											|| (cRel == carl::Relation::EQ)
			){
			std::cout << "Convert big formula..." << std::endl;
			auto res = convertBigFormula(formula);
			SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
			std::cout << "OK" << std::endl;
			return res;
		}else if(Settings::use_rns_transformation && positive && cRel == carl::Relation::EQ && (sum * 2) > cLHS.size()){
			initPrimesTable();
			std::vector<carl::uint> base = calculateRNSBase(formula);
			if(base.size() != 0 && isNonRedundant(base, formula)){
				std::cout << "Rns transformation..." << std::endl;
				auto res = rnsTransformation(formula);
				std::cout << "OK" << std::endl;
				return res;
			}else{
				std::cout << "Forward as arithmetic..." << std::endl;
				auto res = forwardAsArithmetic(formula);
				SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
				std::cout << "OK" << std::endl;
				return res;
			}
		}else{
			auto res = forwardAsArithmetic(formula);
			SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
			return res;
		}

	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::convertSmallFormula(const FormulaT& formula){
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
				}else{
					return forwardAsArithmetic(formula);
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
				}else{
					return forwardAsArithmetic(formula);
				}
			}else{ //lhsCoeff == 0
				if(cRHS > 0){	
					// 0 x2 > 3 or 0 x2 >= 3 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}else if(cRHS == 0 && cRel == carl::Relation::GEQ){
					//0 x2 >= 0 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else if(cRHS == 0 && cRel == carl::Relation::GREATER){
					//0 x2 > 0 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}else if(cRHS < 0){
					// 0 x2 > -3 or 0 x2 >= -3 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else{
					return forwardAsArithmetic(formula);
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
				}else{
					return forwardAsArithmetic(formula);
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
				}else{
					return forwardAsArithmetic(formula);
				}
			}else{ //lhsCoeff == 0
				if(cRHS == 0 && cRel == carl::Relation::LEQ){
					//0 x2 <= 0 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else if(cRHS == 0 && cRel == carl::Relation::LESS){
					//0 x3 < 0 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}else if(cRHS < 0){
					//0 x2 < -3 or 0 x2 <= -3 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}else if(cRHS > 0){
					//0 x2 < 3 or 0 x3 <= 3 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else{
					return forwardAsArithmetic(formula);
				}
			}
		}else if(cRel == carl::Relation::EQ){
			if(lhsCoeff != 0){
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
			}else{
				if(cRHS == 0){
					// 0 x2 = 0 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else if(cRHS != 0){
					// 0 x3 = 3 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}else{
					return forwardAsArithmetic(formula);
				}
			}
		}else if(cRel == carl::Relation::NEQ){
			if(lhsCoeff != 0){
				if(lhsCoeff == cRHS){
					//3 x1 != 3 ===> not x1
					return FormulaT(lhsVar.negated());
				}else if(cRHS == 0){
					//3 x1 != 0 ===> x1
					return FormulaT(lhsVar);
				}else if(lhsCoeff != cRHS){
					//3 x1 != 5 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else{
					return forwardAsArithmetic(formula);
				}
			}else{
				if(cRHS == 0){
					// 0 x2 != 0 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}else if(cRHS != 0){
					// 0 x3 != 3 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else{
					return forwardAsArithmetic(formula);
				}
			}
		}
		return formula;
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::convertBigFormula(const FormulaT& formula){
		const carl::PBConstraint& c = formula.pbConstraint();
		const auto& cLHS 	 = c.getLHS();
		carl::Relation cRel  = c.getRelation();
		auto cVars	  = c.gatherVariables();
		int cRHS 	  = c.getRHS();
		bool positive = true;
		bool negative = true;
		int sum = 0;

		//Filter out constraints with coefficient equal 0
		for(auto it : cLHS){	
			if(it.first == 0){
				return forwardAsArithmetic(formula);
			}
		}

		for(auto it = cLHS.begin(); it != cLHS.end(); it++){
			if(it->first < 0){
				positive = false;
			}else if(it->first > 0){
				negative = false;
			}
			sum += it->first;
		}

		if(!positive && !negative && (cRel == carl::Relation::GEQ || cRel == carl::Relation::LEQ) && sum >= cRHS){
			//-1 x1 +1 x2 >= 0 ===>  not(x1) or x2
			FormulasT newSubformulas;
			for(auto it : cLHS){
				FormulaT f = FormulaT(it.second);
				if(it.first < 0){
					newSubformulas.push_back(f.negated());
				}else{
					newSubformulas.push_back(f);
				}
			}
			return FormulaT(carl::FormulaType::OR, std::move(newSubformulas));
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
			}else{//RHS > 0
				if(sum < cRHS){
					//5 x1 + 2 x2 + 3 x3 >= 20 or 5 x1 + 2 x2 + 3 x3 > 20 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}else if(sum == cRHS && cRel == carl::Relation::GEQ){
					//5 x1 + 2 x2 + 3 x3 >= 10 ===> x1 and x2 and x3
					return generateVarChain(cVars, carl::FormulaType::AND);
				}else if(sum == cRHS && cRel == carl::Relation::GREATER){
					//5 x1 + 2 x2 + 3 x3 > 10 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}//sum > cRHS 
					std::vector<carl::Variable> greaterRHS;
				int subSum = 0;
				for(auto it : cLHS){
					if(it.first >= cRHS){
						greaterRHS.push_back(it.second);
					}
					subSum += it.first;
				}
				if(subSum < cRHS){
					return FormulaT(generateVarChain(greaterRHS, carl::FormulaType::OR));
				}else{
					return forwardAsArithmetic(formula);
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
				}else{ // cRel == carl::Relation::GREATER
					//-5 x1 - 2 x2 - 3 x3 > 0 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);
				}
			}else{ //cRHS < 0
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
				}//sum < cRHS
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
				}else{ //cRel == carl::Relation::LESS
					//5 x1 +2 x2 +3 x3 < 0 ===> FALSE
					return FormulaT(carl::FormulaType::FALSE);	
				}
			}else{ //cRHS > 0
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
				}//sum > cRHS
			}
		}else if(negative && (cRel == carl::Relation::LESS || cRel == carl::Relation::LEQ)){
			if(cRHS > 0){
				//-5 x1 -2 x2 -3 x3 <= 5 or -5 x1 -2 x2 -3 x3 < 5 ===> false -> x1 and x2 and x3 ===> TRUE
				return FormulaT(carl::FormulaType::TRUE);
			}else if(cRHS == 0){
				if(cRel == carl::Relation::LEQ){
					//-5 x1 -2 x2 -3 x3 <= 0 ===> false -> x1 and x2 and x3 ===> TRUE
					return FormulaT(carl::FormulaType::TRUE);
				}else{ //cRel == carl::Relation::LESS
					//-5 x1 -2 x2 -3 x3 < 0 ===> true -> x1 or x2 or x3
					FormulaT subformulaA = FormulaT(carl::FormulaType::TRUE);
					FormulaT subformulaB = generateVarChain(cVars, carl::FormulaType::OR);
					return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
				}
			}else{ //cRHS < 0
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
				}// sum < cRHS
			}
		}else if(cRel == carl::Relation::EQ){
			if(sum == cRHS){
				//5 x1 +2 x2 +3 x3 = 10 ===> x1 and x2 and x3
				std::cout << "HIER 1" << std::endl;
				return generateVarChain(cVars, carl::FormulaType::AND);
			}else if(sum != cRHS && cRHS == 0){
				//5 x1 +2 x2 +3 x3 = 0 ===> (x1 or x2 or x3 -> false)
				std::cout << "HIER 2" << std::endl;
				FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::OR);
				FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
				return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);				
			}else{
				std::cout << "HIER 3" << std::endl;
			 	return forwardAsArithmetic(formula);
			 }		
		}else if(cRel == carl::Relation::NEQ){
			if(sum != cRHS && cRHS == 0){
				//5 x1 +2 x2 +3 x3 = 0 ===> not(x1 and x2 and x3)
				FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::AND);
				return FormulaT(carl::FormulaType::NOT, subformulaA);
			}else{
				return forwardAsArithmetic(formula);
			}	
		}
	return formula;
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::generateVarChain(const std::vector<carl::Variable>& vars, carl::FormulaType type){
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
		const carl::PBConstraint& c = formula.pbConstraint();
		const auto& cLHS = c.getLHS();
		carl::Relation cRel  = c.getRelation();
		int cRHS = c.getRHS();
		auto variables = c.gatherVariables();

		for(auto it : variables){
			mVariablesCache.insert(std::pair<carl::Variable, carl::Variable>(it, carl::freshVariable(carl::VariableType::VT_INT)));
		}

		Poly lhs;
		for(auto it : cLHS){
			auto finder = mVariablesCache.find(it.second);
			carl::Variable curVariable = finder->second;
			Poly pol(curVariable);
			lhs = lhs + Rational(it.first) * pol;
		}
		lhs = lhs - Rational(cRHS);
		FormulaT subformulaA = FormulaT(lhs, cRel);

		//Adding auxiliary constraint to ensure variables are assigned to 1 or 0.
		FormulaT subformulaB = createAuxiliaryConstraint(formula);
		FormulaT subformulaC = FormulaT(carl::FormulaType::AND, subformulaA, subformulaB);

		//Adding auxiliary constraint to interconnect the bool and int variables
		FormulaT subformulaD = interconnectVariables(formula);

		return FormulaT(carl::FormulaType::AND, subformulaC, subformulaD);
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::createAuxiliaryConstraint(const FormulaT& formula){
		const carl::PBConstraint& c = formula.pbConstraint();
		auto boolVars        = c.gatherVariables();
		std::vector<carl::Variable> intVars;
		for(auto it : boolVars){
			if(std::find(mCheckedVars.begin(), mCheckedVars.end(), it) == mCheckedVars.end()){ 
				//There are no auxiliary constraints for this variable
				intVars.push_back(mVariablesCache.find(it)->second);
				mCheckedVars.push_back(it);
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
		const carl::PBConstraint& c = formula.pbConstraint();
		auto boolVars 		 = c.gatherVariables();
		std::map<carl::Variable, carl::Variable> varsMap;

		for(auto var : boolVars){
			varsMap.insert(*mVariablesCache.find(var));
		}

		FormulasT newSubformulas;
		for(auto var : varsMap){
			FormulaT boolVar = FormulaT(var.first);
			Poly intVar(var.second);
			FormulaT subformulaA = FormulaT(intVar - Rational(1), carl::Relation::EQ);
			FormulaT subformulaB = FormulaT(carl::FormulaType::IMPLIES, boolVar, subformulaA);
			FormulaT subformulaC = FormulaT(intVar, carl::Relation::EQ);
			FormulaT subformulaD = FormulaT(carl::FormulaType::IMPLIES, boolVar.negated(), subformulaC);
			FormulaT newFormula  = FormulaT(carl::FormulaType::AND, subformulaB, subformulaD);
			newSubformulas.push_back(newFormula);
		}
		return FormulaT(carl::FormulaType::AND, std::move(newSubformulas));

	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::rnsTransformation(const FormulaT& formula){
		const carl::PBConstraint& c = formula.pbConstraint();
	    const auto& cLHS = c.getLHS();
	    const int cRHS = c.getRHS();
	    std::vector<carl::uint> base = calculateRNSBase(formula);

	    FormulasT subformulas;
	        for(auto i : base){
	            std::vector<std::pair<int, carl::Variable>> newLHS;
	           	int newRHS = cRHS % (int) i;
	            carl::PBConstraint newConstraint;
	            for(auto it : cLHS){
	            	if((it.first % (int) i) != 0){
	            		newLHS.push_back(std::pair<int, carl::Variable>(it.first % (int) i, it.second));
	            	}

	            }

	            if(newLHS.size() == 0 && newRHS > 0){
	            	return FormulaT(carl::FormulaType::FALSE);
	            }
	            
	            int t = 0;
	            for(auto it : newLHS){
	                t += it.first;
	            }
	            t = std::floor((t - newRHS)/ i );

	            for(int i = 0; i < t; i++){
	                newLHS.push_back(std::pair<int, carl::Variable>(-t, carl::freshVariable(carl::VariableType::VT_BOOL)));
	            }
	            
	            newConstraint.setLHS(newLHS);
	            newConstraint.setRHS(newRHS);
	            newConstraint.setRelation(carl::Relation::EQ);
	            subformulas.push_back(FormulaT(newConstraint));
	        }
	    FormulaT f = FormulaT(carl::FormulaType::AND, std::move(subformulas));
	    return checkFormulaType(f);
	}


    template<typename Settings>
    std::vector<carl::uint> PBPPModule<Settings>::calculateRNSBase(const FormulaT& formula){
    	const carl::PBConstraint& c = formula.pbConstraint();	
	    const auto& cLHS = c.getLHS();
	    int max = INT_MIN;
	    int min = INT_MAX;

	    std::vector<std::pair<int, carl::uint>> freq;
	    carl::uint sum = 0;
	    carl::uint product = 1;
	        
	    for(auto it : cLHS){
	        if(it.first > max){
	            max = it.first;
	        }else{
	       		min = it.first;
	        }
	        sum += (carl::uint) it.first;
        }

        for(auto it : cLHS){
        	std::vector<carl::uint> v = integerFactorization(it.first);
        	std::sort(v.begin(), v.end());
        	v.erase( unique( v.begin(), v.end() ), v.end() );

        	for(auto i : v){
        		auto elem = std::find_if(freq.begin(), freq.end(), 
	            	[&] (const pair<int, carl::uint>& elem){
	              		return elem.second == i;
	            		});
        		if(elem != freq.end()){
	            	auto distance = std::distance(freq.begin(), elem);
	            	freq[distance].first = freq[distance].first + 1;
	        	}else{
	            	freq.push_back(std::pair<int, carl::uint>(1, i));
	        	}
        	}
        	
        }

        std::sort(freq.begin(), freq.end(),
	        [&](const pair<int, carl::uint> &p1, const pair<int, carl::uint> &p2)
	            {
	              	if(p1.first == p2.first){
	                    return (p1.second < p2.second);
	                }else{
	                   	return(p1.first > p2.first);
	                }
	            });

       	std::vector<carl::uint> base;
	    for(auto it : freq){
	    	if(it.second != 0){
	    		product *= it.second;
	        	if(product <= sum){
	            	base.push_back(it.second);	
	        	}else{
	            	base.push_back(it.second);
	            	break;
	        	}
	    	}

	    }
		return base;
     }
  

    template<typename Settings>
    std::vector<carl::uint>PBPPModule<Settings>::integerFactorization(const int& coeff){ 
    	if(coeff == 2){
    		return std::vector<carl::uint>((carl::uint) 2);
    	}else if(coeff <= 100){
    		return mPrimesTable[coeff];
    	}

    	std::vector<carl::uint> primes;
    	int x = (int) std::ceil(sqrt(coeff));
    	int y = (x * x) - coeff;
    	int r = (int) sqrt(y);

		if(coeff % 2 == 0){
			primes.push_back((carl::uint) 2);
			if(coeff / 2 > 2){
				std::vector<carl::uint> v = integerFactorization(coeff / 2);
				primes.insert(primes.end(), v.begin(), v.end());
			}
		}else{
		    while(y >  r * r){
	    		x++;
	    		y = (x * x) - coeff;
	    		r = (int) sqrt(y);
	    	}

	    	int first = x + r;
	    	int second  = x - r;

	    	if(first > 1){
	    		if(first <= 100){
	    			std::vector<carl::uint> v = mPrimesTable[(int) first];
	    			primes.insert(primes.end(), v.begin(), v.end());
	    			
	    		}else{
	    			carl::PrimeFactory<carl::uint> pFactory;
	    			carl::uint prime = pFactory[24];
	    			while(prime < (carl::uint) first){
	    				prime = pFactory.nextPrime();
	    			}
	    			if(prime == (carl::uint) first){
	    				//first is a big prime number
	    				primes.push_back((carl::uint)first);
	    			}else{
	    				//first is not a prime number
	    				std::vector<carl::uint> v = integerFactorization(first);
	    				primes.insert(primes.end(), v.begin(), v.end());
	    			}
	    		}
	    	}

	    	if(second > 1){
	    		if(second <= 100){
	    			std::vector<carl::uint> v = mPrimesTable[(int) second];
	    			primes.insert(primes.end(), v.begin(), v.end());		
	    		}else{
	    			carl::PrimeFactory<carl::uint> pFactory;
	    			carl::uint prime = pFactory[24];
	    			while(prime < (carl::uint) second){
	    				prime = pFactory.nextPrime();
	    			}
	    			if(prime == (carl::uint) second){
	    				//second is a big prime number
	    				primes.push_back((carl::uint) second);
	    			}else{
	    				//second is not a prime number
	    				std::vector<carl::uint> v = integerFactorization(second);
	    				primes.insert(primes.end(), v.begin(), v.end());
	    			}
	    		}
	    	}
	    }

    	return primes;
    }

    
    template<typename Settings>
    bool PBPPModule<Settings>::isNonRedundant(const std::vector<carl::uint>& base, const FormulaT& formula){
        const carl::PBConstraint& c = formula.pbConstraint();	
        const auto& cLHS = c.getLHS();
        int max = INT_MIN;
        int product = 1;
        
        for(auto it : cLHS){
            if(it.first > max){
                max = it.first;
            }
        }
        for(auto it : base){
            product *= it;
        }
        
        for(auto it : base){
            if(it >= (carl::uint) max){
                return false;
            }
        } 
        return true;
    }


    template<typename Settings>
	void PBPPModule<Settings>::initPrimesTable(){
		//The 0 and 1 MUST be here in order to pick the right factorization!
		mPrimesTable = {{0}, {1}, {2}, {3}, {2, 2}, {5}, {2, 3}, {7}, {2, 2, 2}, {3, 3}, {2, 5}, {11}, {2, 2, 3},
						{13}, {2, 7}, {3, 5}, {2, 2, 2, 2}, {17}, {2, 3, 3}, {19}, {2, 2, 5}, {3, 7}, {2, 11},
						{23}, {2, 2, 2, 3}, {5, 5}, {2, 13}, {3, 3, 3}, {2, 2, 7}, {29}, {2, 3, 5}, {31}, 
						{2, 2, 2, 2, 2}, {3, 11}, {2, 17}, {5, 7}, {2, 2, 3, 3}, {37}, {2, 19}, {3, 13}, {2, 2, 2, 5},
						{41}, {2, 3, 7}, {43}, {2, 2, 11}, {3, 3, 5}, {2, 23}, {47}, {2, 2, 2, 2, 3}, {7 ,7}, {2, 5, 5},
						{3, 17}, {2, 2, 13}, {53}, {2, 3, 3, 3}, {5, 11}, {2, 2, 2, 7}, {3, 19}, {2, 29}, {59}, 
						{2, 2, 3, 5}, {61}, {2, 31}, {3, 3, 7}, {2, 2, 2, 2, 2, 2}, {5, 13}, {2, 3, 11}, {67},
						{2, 2, 17}, {3, 23}, {2, 5, 7}, {71}, {2, 2, 2, 3, 3}, {73}, {2, 37}, {3, 5, 5}, {2, 2, 19}, 
						{7, 11}, {2, 3, 13}, {79}, {2, 2, 2, 2, 5}, {3, 3, 3, 3}, {2, 41}, {83}, {2, 2, 3, 7}, {5, 17},
						{2, 43}, {3, 29}, {2, 2, 2, 11}, {89}, {2, 3, 3, 5}, {7, 13}, {2, 2, 23}, {3, 31}, {2, 47},
						{5, 19}, {2, 2, 2, 2, 2, 3}, {97}, {2, 7, 7}, {3, 3, 11}, {2, 2, 5, 5}};
	}
}

#include "Instantiation.h"
