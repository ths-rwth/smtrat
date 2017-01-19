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
		std::vector<std::pair<int, carl::Variable>> cLHS = c.getLHS();
		const auto& cLHS = c.getLHS();
		carl::Relation cRel = c.getRelation();
		int cRHS = c.getRHS();
		int sum = 0;
		bool positive = true;
		bool negative = true;
		for(auto it = cLHS.begin(); it != cLHS.end(); it++){
			sum += it->first;
			if(it->first < 0){
				positive = false;
			}else if(it->first > 0){
				negative = false;
			}
		}
		if(cLHS.size() < 4 
			&& !((cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS) && sum > cRHS && cLHS.size() > 1) 
				&& !(positive && cRHS > 0 && sum > cRHS 
						&& (cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER || cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS))
					&& !(negative && cRHS < 0 && (cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER) && sum > cRHS)
						&& !(negative && cRHS < 0 && (cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS) && sum < cRHS)
							&& !((positive || negative) && cRel == carl::Relation::NEQ && sum != cRHS && cRHS != 0)
								&& !((positive || negative) && cRel == carl::Relation::NEQ && sum == cRHS && cRHS != 0)
									&& (negative || positive)
			){
			auto res = forwardAsBoolean(formula);
			SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
			return res;
		}
		return forwardAsArithmetic(formula);
	}



	template<typename Settings>
	FormulaT PBPPModule<Settings>::convertSmallFormulaToBoolean(const FormulaT& formula){
		carl::PBConstraint c = formula.pbConstraint();
		std::vector<std::pair<int, carl::Variable>> cLHS = c.getLHS();
		const auto& cLHS = c.getLHS();

		carl::Relation cRel = c.getRelation();
		int cRHS = c.getRHS();
		std::vector<carl::Variable> cVars= c.gatherVariables();
		bool positive = true;
		bool negative = true;
		int sum = 0;

		std::pair<int, carl::Variable> varsMinimum = *cLHS.begin();
		int lhsCoeff = cLHS.begin()->first;

		std::pair<carl::Variable,int> varsMinimum = cLHS.front();


		for(auto it = cLHS.begin(); it != cLHS.end(); it++){
			if(it->first < 0){
				positive = false;
			}else if(it->first > 0){
				negative = false;
			}
			sum += it->first;
			if(it->first < varsMinimum.first){

				varsMinimum.first = it->first;
				varsMinimum.second = it->second;
				varsMinimum = *it;
			}
		}

		if((cLHS.begin()->second > 0 && (cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER) && cRHS < 0) /* 5 x1 >= -2 or 5 x1 > -2*/ 
					|| (cLHS.begin()->second > 0 && cRel == carl::Relation::GEQ && cRHS == 0) /*5 x1 >= 0*/
						|| (cLHS.begin()->second < 0 && cRel == carl::Relation::LEQ && cRHS == 0) /*-5 x1 <= 0*/
							|| (cLHS.begin()->second < 0 && (cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS) && cRHS > 0) /*-5 x1 <= 2 or -5 x1 < 2*/
								|| ((cLHS.begin()->second < 0 && (cRel == carl::Relation::GREATER || cRel == carl::Relation::GEQ) && cRHS < 0) 
									&& ((cLHS.begin()->second > cRHS) || (cLHS.begin()->second == cRHS && cRel == carl::Relation::GEQ))) /*-2 x1 >= -5 or -2 x1 > -5 or -5 x1 >= -5*/
									|| ((cLHS.begin()->second > 0 && (cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS) && cRHS > 0) 
										&& ((cLHS.begin()->second < cRHS) ||(cLHS.begin()->second == cRHS && cRel == carl::Relation:: LEQ))) /*2 x1 <= 5 or 2 x1 < 5 or 5 x1 <= 5*/
									){
				//===> false -> x1
				return FormulaT(carl::FormulaType::TRUE);
			}else if((cLHS.begin()->second > 0 && cRel == carl::Relation::GREATER && cRHS == 0) /*5 x1 > 0*/
						|| (cLHS.begin()->second < 0 && cRel == carl::Relation::LESS && cRHS == 0) /*-5 x1 < 0*/
							|| (cRel == carl::Relation::EQ && cLHS.begin()->second == cRHS) /*a x1 == a*/
								|| ((cLHS.begin()->second > 0 && (cRel == carl::Relation::GREATER || cRel == carl::Relation::GEQ) && cRHS > 0) 
									&& ((cLHS.begin()->second > cRHS) || (cLHS.begin()->second == cRHS && cRel == carl::Relation::GEQ))) /*5 x1 >= 2 or 5 x1 > 2 or 5 x1 >= 5*/
									|| ((cLHS.begin()->second < 0 && (cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS) && cRHS < 0) 
										&& ((cLHS.begin()->second < cRHS) || (cLHS.begin()->second == cRHS && cRel == carl::Relation::LEQ))) /*-5 x1 <= -2 or -5 x1 < -2 or -5 x1 <= -5*/
									){
				//===> true -> x1
	 			return FormulaT(cLHS.begin()->first);
			}else if((cLHS.begin()->second < 0 && cRel == carl::Relation:: GEQ && cRHS == 0) /*-5 x1 >= 0 */
						|| (cLHS.begin()->second > 0 && cRel == carl::Relation::LEQ && cRHS == 0) /*5 x1 <= 0*/
							|| ((cLHS.begin()->second < 0 && (cRel == carl::Relation::GREATER || cRel == carl::Relation::GEQ) && cRHS < 0) 
								&& ((cLHS.begin()->second < cRHS) || (cLHS.begin()->second == cRHS && cRel == carl::Relation::GREATER))) /*-5 x1 >= -2 or -5 x1 > -2 or -5 x1 > -5*/
								|| ((cLHS.begin()->second > 0 && (cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS) && cRHS > 0) 
									&& ((cLHS.begin()->second > cRHS) || (cLHS.begin()->second > cRHS && cRel == carl::Relation:: LESS))) /*5 x1 <= 2 or 5 x1 < 2*/
								){
				//===> x1 -> false 
				FormulaT subformulaA = FormulaT(cLHS.begin()->first);
				FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
				FormulaT f = FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
				SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << f);
				return f;
			}else if((cLHS.begin()->second < 0 && cRel == carl::Relation::GREATER && cRHS == 0) /* -5 x1 > 0*/
						|| (cLHS.begin()->second < 0 && (cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER) && cRHS > 0)/*-5 x1 >= 2 or -5 x1 > 2*/
							|| (cLHS.begin()->second > 0 && (cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS) && cRHS < 0) /*5 x1 <= -2 or 5 x1 < -2*/
								|| (cLHS.begin()->second > 0 && cRel == carl::Relation::LESS && cRHS == 0) /*5 x1 < 0*/
									|| ((cLHS.begin()->second > 0 && (cRel == carl::Relation::GREATER || cRel == carl::Relation::GEQ) && cRHS > 0) 
										&& ((cLHS.begin()->second < cRHS) ||(cLHS.begin()->second == cRHS && cRel == carl::Relation::GREATER)))	/*2 x1 >= 5 or 2 x1 > 5 or 5 x1 > 5*/
										|| ((cLHS.begin()->second < 0 && (cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS) && cRHS < 0) 
											&& ((cLHS.begin()-> second > cRHS) || (cLHS.begin()->second == cRHS && cRel == carl::Relation::LESS))) /*-2 x1 <= -5 or -2 x1 < -5 or -5 x1 < -5*/
										){
				//===> false 
				FormulaT f = FormulaT(carl::FormulaType::FALSE);
				SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> FALSE");
				return f;
			}
		return formula;
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::convertBigFormulaToBoolean(const FormulaT& formula){
		carl::PBConstraint c = formula.pbConstraint();
		std::vector<std::pair<int, carl::Variable>> cLHS = c.getLHS();
		carl::Relation cRel = c.getRelation();
		int cRHS = c.getRHS();
		std::vector<carl::Variable> cVars= c.gatherVariables();
		bool positive = true;
		bool negative = true;
		int sum = 0;
		std::pair<int, carl::Variable> varsMinimum = *cLHS.begin();

		for(auto it = cLHS.begin(); it != cLHS.end(); it++){
			if(it->first < 0){
				positive = false;
			}else if(it->first > 0){
				negative = false;
			}
			sum += it->first;
			if(it->first < varsMinimum.first){
				varsMinimum.first = it->first;
				varsMinimum.second = it->second;
			}
		}

		if(positive && (cRel == carl::Relation::GREATER || cRel == carl::Relation::GEQ)){
			if(cRHS < 0){
				//5 x1 + 2 x2 + 3 x3 >= -5 or 5 x1 + 2 x2 + 3 x3 > -5 
				//===> false -> x1 AND x2 AND x3 ===> TRUE
				FormulaT f = FormulaT(carl::FormulaType::TRUE);
				return f;
				}else if(cRHS == 0){
					if(cRel == carl::Relation::GEQ){
						// 5 x1 + 2 x2 + 3 x3 >= 0 ===> false -> x1 AND x2 AND x3 ===> TRUE
						FormulaT f = FormulaT(carl::FormulaType::TRUE);
						return f;
					}
					// 5 x1 + 2 x2 + 3 x3 > 0 ===> x1 or x2 or x3
					FormulaT f = generateVarChain(cVars, carl::FormulaType::OR);
					return f;
				}//RHS > 0
					if(sum < cRHS){
						//5 x1 + 2 x2 + 3 x3 >= 20 or 5 x1 + 2 x2 + 3 x3 > 20 ===> FALSE
						FormulaT f = FormulaT(carl::FormulaType::FALSE);
	 					return f;
					}else if(sum == cRHS && cRel == carl::Relation::GEQ){
						//5 x1 + 2 x2 + 3 x3 >= 10 ===> x1 and x2 and x3
						FormulaT f = generateVarChain(cVars, carl::FormulaType::AND);
						return f;
					}else if(sum == cRHS && cRel == carl::Relation::GREATER){
						//5 x1 + 2 x2 + 3 x3 > 10 ===> FALSE
						FormulaT f = FormulaT(carl::FormulaType::FALSE);
	 					return f;					}
			}else if(negative && (cRel == carl::Relation::GREATER || cRel == carl::Relation::GEQ)){
				if(cRHS > 0){
					//-5 x1 - 2 x2 - 3 x3 >= 5 or -5 x1 - 2 x2 - 3 x3 > 5 ===> FALSE
					FormulaT f = FormulaT(carl::FormulaType::FALSE);
					return f;
				}else if(cRHS == 0){
					if(cRel == carl::Relation::GEQ){
						//-5 x1 - 2 x2 - 3 x3 >= 0 ===> (x1 or x2 or x3) -> false
						FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::OR);
						FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
						FormulaT f = FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
						return f;
					}
					//-5 x1 - 2 x2 - 3 x3 > 0 ===> FALSE
					FormulaT f = FormulaT(carl::FormulaType::FALSE);
	 				return f;
				}else if(cRHS < 0){
					if(sum < cRHS){
						//-5 x1 - 2 x2 - 3 x3 >= -5 or -5 x1 - 2 x2 - 3 x3 > -5 ===> FALSE
						FormulaT f = FormulaT(carl::FormulaType::FALSE);
	 					return f;
					}else if(sum == cRHS && cRel == carl::Relation::GEQ){
						//-5 x1 - 2 x2 - 3 x3 >= -10  ===> false -> x1 and x2 and x3 ===> TRUE
						FormulaT f = FormulaT(carl::FormulaType::TRUE);
						return f;
					}else if(sum == cRHS && cRel == carl::Relation::GREATER){
						//-5 x1 - 2 x2 - 3 x3 > -10  ===> x1 and x2 and x3 -> false
						FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::AND);
						FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
						FormulaT f = FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
						return f;
					}
				}
			}else if(positive && (cRel == carl::Relation::LESS || cRel == carl::Relation::LEQ)){
				if(cRHS < 0){
					//5 x1 +2 x2 +3 x3 <= -5 or 5 x1 +2 x2 +3 x3 < -5 ===> FALSE
					FormulaT f = FormulaT(carl::FormulaType::FALSE);
					return f;
				}else if(cRHS == 0){
					if(cRel == carl::Relation::LEQ){
						//5 x1 +2 x2 +3 x3 <= 0 ===> (x1 or x2 or x3) -> false
						FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::OR);
						FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
						FormulaT f = FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
						return f;
					}
					//5 x1 +2 x2 +3 x3 < 0 ===> FALSE
					FormulaT f = FormulaT(carl::FormulaType::FALSE);
	 				return f;
				}else if(cRHS > 0){
					if(sum > cRHS){
						//5 x1 +2 x2 +3 x3 < 0 ===> FALSE
						FormulaT f = FormulaT(carl::FormulaType::FALSE);
	 					return f;
					}else if(sum == cRHS && cRel == carl::Relation::LEQ){
						//5 x1 +2 x2 +3 x3 <= 10 ===> false -> x1 and x2 and x3 ===> TRUE
						FormulaT f = FormulaT(carl::FormulaType::TRUE);
						return f;
					}else if(sum == cRHS && cRel == carl::Relation::LESS){
						//5 x1 +2 x2 +3 x3 < 10 ===> x1 and x2 and x3 -> false
						FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::AND);
						FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
						FormulaT f = FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
						return f;
					}else if(sum < cRHS){
						//5 x1 +2 x2 +3 x3 <= 20 or 5 x1 +2 x2 +3 x3 < 20 ===> false -> x1 and x2 and x3 ===> TRUE
						FormulaT f = FormulaT(carl::FormulaType::TRUE);
						return f;
					}
				}
			}else if(negative && (cRel == carl::Relation::LESS || cRel == carl::Relation::LEQ)){
				if(cRHS > 0){
					//-5 x1 -2 x2 -3 x3 <= 5 or -5 x1 -2 x2 -3 x3 < 5 ===> false -> x1 and x2 and x3 ===> TRUE
					FormulaT f = FormulaT(carl::FormulaType::TRUE);
					return f;
				}else if(cRHS == 0){
					if(cRel == carl::Relation::LEQ){
						//-5 x1 -2 x2 -3 x3 <= 0 ===> false -> x1 and x2 and x3 ===> TRUE
						FormulaT f = FormulaT(carl::FormulaType::TRUE);
						return f;
					}
					//-5 x1 -2 x2 -3 x3 < 0 ===> true -> x1 or x2 or x3
					FormulaT subformulaA = FormulaT(carl::FormulaType::TRUE);
					FormulaT subformulaB = generateVarChain(cVars, carl::FormulaType::OR);
					FormulaT f = FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
					return f;
				}else if(cRHS < 0){
					if(sum > cRHS){
						//-5 x1 -2 x2 -3 x3 < -15 or -5 x1 -2 x2 -3 x3 <= -15 ===> FALSE
						FormulaT f = FormulaT(carl::FormulaType::FALSE);
	 					return f;
					}else if(sum == cRHS && cRel == carl::Relation::LEQ){
						//-5 x1 -2 x2 -3 x3 <= -10 ===> x1 and x2 and x3 -> false
						FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::AND);
						FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
						FormulaT f = FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
						return f;
					}else if(sum == cRHS && cRel == carl::Relation::LESS){
						//-5 x1 -2 x2 -3 x3 < -10 ===> FALSE
						FormulaT f = FormulaT(carl::FormulaType::FALSE);;
	 					return f;
					}
				}
			}else if(cRel == carl::Relation::EQ){
				if(sum != cRHS && cRHS != 0){
					//5 x1 +2 x2 +3 x3 = 5 ===> FALSE
						FormulaT f = FormulaT(carl::FormulaType::FALSE);
						return f;
				}else if(sum != cRHS && cRHS == 0){
					//5 x1 +2 x2 +3 x3 = 0 ===> (x1 or x2 or x3 -> false)
					FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::OR);
					FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
					FormulaT f = FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
					return f;
				}
				//5 x1 +2 x2 +3 x3 = 10 ===> x1 and x2 and x3
					FormulaT f = generateVarChain(cVars, carl::FormulaType::AND);
					return f;
			}else if(cRel == carl::Relation::NEQ){
				if(sum != cRHS && cRHS == 0){
					//5 x1 +2 x2 +3 x3 = 0 ===> x1 and x2 and x3 
					FormulaT f = generateVarChain(cVars, carl::FormulaType::AND);
					return f;
				}	
			}if(positive && (cRel == carl::Relation::GREATER || cRel == carl::Relation::GEQ)){
				if(cRHS < 0){
					//5 x1 + 2 x2 + 3 x3 >= -5 or 5 x1 + 2 x2 + 3 x3 > -5 
					//===> false -> x1 AND x2 AND x3 ===> TRUE
					FormulaT f = FormulaT(carl::FormulaType::TRUE);
					return f;
				}else if(cRHS == 0){
					if(cRel == carl::Relation::GEQ){
						// 5 x1 + 2 x2 + 3 x3 >= 0 ===> false -> x1 AND x2 AND x3 ===> TRUE
						FormulaT f = FormulaT(carl::FormulaType::TRUE);
						return f;
					}
					// 5 x1 + 2 x2 + 3 x3 > 0 ===> x1 or x2 or x3
					FormulaT f = generateVarChain(cVars, carl::FormulaType::OR);
					return f;
				}//RHS > 0
					if(sum < cRHS){
						//5 x1 + 2 x2 + 3 x3 >= 20 or 5 x1 + 2 x2 + 3 x3 > 20 ===> FALSE
						FormulaT f = FormulaT(carl::FormulaType::FALSE);
	 					return f;
					}else if(sum == cRHS && cRel == carl::Relation::GEQ){
						//5 x1 + 2 x2 + 3 x3 >= 10 ===> x1 and x2 and x3
						FormulaT f = generateVarChain(cVars, carl::FormulaType::AND);
						return f;
					}else if(sum == cRHS && cRel == carl::Relation::GREATER){
						//5 x1 + 2 x2 + 3 x3 > 10 ===> FALSE
						FormulaT f = FormulaT(carl::FormulaType::FALSE);
	 					return f;					}
			}else if(negative && (cRel == carl::Relation::GREATER || cRel == carl::Relation::GEQ)){
				if(cRHS > 0){
					//-5 x1 - 2 x2 - 3 x3 >= 5 or -5 x1 - 2 x2 - 3 x3 > 5 ===> FALSE
					FormulaT f = FormulaT(carl::FormulaType::FALSE);
					return f;
				}else if(cRHS == 0){
					if(cRel == carl::Relation::GEQ){
						//-5 x1 - 2 x2 - 3 x3 >= 0 ===> (x1 or x2 or x3) -> false
						FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::OR);
						FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
						FormulaT f = FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
						return f;
					}
					//-5 x1 - 2 x2 - 3 x3 > 0 ===> FALSE
					FormulaT f = FormulaT(carl::FormulaType::FALSE);
	 				return f;
				}else if(cRHS < 0){
					if(sum < cRHS){
						//-5 x1 - 2 x2 - 3 x3 >= -5 or -5 x1 - 2 x2 - 3 x3 > -5 ===> FALSE
						FormulaT f = FormulaT(carl::FormulaType::FALSE);
						return f;
					}else if(sum == cRHS && cRel == carl::Relation::GEQ){
						//-5 x1 - 2 x2 - 3 x3 >= -10  ===> false -> x1 and x2 and x3 ===> TRUE
						FormulaT f = FormulaT(carl::FormulaType::TRUE);
						return f;
					}else if(sum == cRHS && cRel == carl::Relation::GREATER){
						//-5 x1 - 2 x2 - 3 x3 > -10  ===> x1 and x2 and x3 -> false
						FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::AND);
						FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
						FormulaT f = FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
						return f;
					}
				}
			}else if(positive && (cRel == carl::Relation::LESS || cRel == carl::Relation::LEQ)){
				if(cRHS < 0){
					//5 x1 +2 x2 +3 x3 <= -5 or 5 x1 +2 x2 +3 x3 < -5 ===> FALSE
					FormulaT f = FormulaT(carl::FormulaType::FALSE);
	 				return f;
				}else if(cRHS == 0){
					if(cRel == carl::Relation::LEQ){
						//5 x1 +2 x2 +3 x3 <= 0 ===> (x1 or x2 or x3) -> false
						FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::OR);
						FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
						FormulaT f = FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
						return f;
					}
					//5 x1 +2 x2 +3 x3 < 0 ===> FALSE
					FormulaT f = FormulaT(carl::FormulaType::FALSE);
	 				return f;
				}else if(cRHS > 0){
					if(sum > cRHS){
						//5 x1 +2 x2 +3 x3 < 0 ===> FALSE
						FormulaT f = FormulaT(carl::FormulaType::FALSE);
	 					return f;
					}else if(sum == cRHS && cRel == carl::Relation::LEQ){
						//5 x1 +2 x2 +3 x3 <= 10 ===> false -> x1 and x2 and x3 ===> TRUE
						FormulaT f = FormulaT(carl::FormulaType::TRUE);
						return f;
					}else if(sum == cRHS && cRel == carl::Relation::LESS){
						//5 x1 +2 x2 +3 x3 < 10 ===> x1 and x2 and x3 -> false
						FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::AND);
						FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
						FormulaT f = FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
						return f;
					}else if(sum < cRHS){
						//5 x1 +2 x2 +3 x3 <= 20 or 5 x1 +2 x2 +3 x3 < 20 ===> false -> x1 and x2 and x3 ===> TRUE
						FormulaT f = FormulaT(carl::FormulaType::TRUE);
						return f;
					}
				}
			}else if(negative && (cRel == carl::Relation::LESS || cRel == carl::Relation::LEQ)){
				if(cRHS > 0){
					//-5 x1 -2 x2 -3 x3 <= 5 or -5 x1 -2 x2 -3 x3 < 5 ===> false -> x1 and x2 and x3 ===> TRUE
					FormulaT f = FormulaT(carl::FormulaType::TRUE);
					return f;
				}else if(cRHS == 0){
					if(cRel == carl::Relation::LEQ){
						//-5 x1 -2 x2 -3 x3 <= 0 ===> false -> x1 and x2 and x3 ===> TRUE
						FormulaT f = FormulaT(carl::FormulaType::TRUE);
						return f;
					}
					//-5 x1 -2 x2 -3 x3 < 0 ===> x1 or x2 or x3
					FormulaT f = generateVarChain(cVars, carl::FormulaType::OR);
					return f;
				}else if(cRHS < 0){
					if(sum > cRHS){
						//-5 x1 -2 x2 -3 x3 < -15 or -5 x1 -2 x2 -3 x3 <= -15 ===> FALSE
						FormulaT f = FormulaT(carl::FormulaType::FALSE);
	 					return f;
					}else if(sum == cRHS && cRel == carl::Relation::LEQ){
						//-5 x1 -2 x2 -3 x3 <= -10 ===> x1 and x2 and x3 -> false
						FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::AND);
						FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
						FormulaT f = FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
						return f;
					}else if(sum == cRHS && cRel == carl::Relation::LESS){
						//-5 x1 -2 x2 -3 x3 < -10 ===> FALSE
						FormulaT f = FormulaT(carl::FormulaType::FALSE);
	 					return f;
					}
				}
			}else if(cRel == carl::Relation::EQ){
				if(sum != cRHS && cRHS != 0){
					//5 x1 +2 x2 +3 x3 = 5 ===> FALSE
						FormulaT f = FormulaT(carl::FormulaType::FALSE);
	 					return f;
				}else if(sum != cRHS && cRHS == 0){
					//5 x1 +2 x2 +3 x3 = 0 ===> (x1 or x2 or x3 -> false)
					FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::OR);
					FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
					FormulaT f = FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
					return f;
				}
				//5 x1 +2 x2 +3 x3 = 10 ===> x1 and x2 and x3
					FormulaT f = generateVarChain(cVars, carl::FormulaType::AND);
					return f;
			}else if(cRel == carl::Relation::NEQ){
				if(sum != cRHS && cRHS == 0){
					//5 x1 +2 x2 +3 x3 = 0 ===> x1 and x2 and x3 
					FormulaT f = generateVarChain(cVars, carl::FormulaType::AND);
					return f;
				}	
			}
		return formula;
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::forwardAsBoolean(const FormulaT& formula){
		std::cout << "FORWARDASBOOLEAN" << std::endl;
		carl::PBConstraint c = formula.pbConstraint();
		std::vector<std::pair<int, carl::Variable>> cLHS = c.getLHS();
		carl::Relation cRel = c.getRelation();
		int cRHS = c.getRHS();
		std::vector<carl::Variable> cVars= c.gatherVariables();
		bool positive = true;
		bool negative = true;
		int sum = 0;
		std::pair<int, carl::Variable> varsMinimum = *cLHS.begin();

		for(auto it = cLHS.begin(); it != cLHS.end(); it++){
			if(it->first < 0){
				positive = false;
			}else if(it->first > 0){
				negative = false;
			}
			sum += it->first;
			if(it->first < varsMinimum.first){
				varsMinimum.first = it->first;
				varsMinimum.second = it->second;
			}
		}

		if(cLHS.size() == 1){
			return convertBigFormulaToBoolean(formula);
		}else if(cLHS.size() <= 3){
			return convertBigFormulaToBoolean(formula);
		}
	 	return formula;
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::generateVarChain(std::vector<carl::Variable>& vars, carl::FormulaType type){
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
		for(auto it = variables.begin(); it != variables.end(); it++){
			auto finderIt = mVariablesCache.find(*it);
			if(finderIt == mVariablesCache.end()){
				mVariablesCache.insert(std::pair<carl::Variable, carl::Variable>(*it, carl::freshVariable(carl::VariableType::VT_INT)));
			}
		}
		Poly lhs;
		carl::PBConstraint c = formula.pbConstraint();
		std::vector<std::pair<int, carl::Variable>> cLHS = c.getLHS();
		for(auto it = cLHS.begin(); it != cLHS.end(); it++){
			auto finder = mVariablesCache.find(it->second);	
			carl::Variable curVariable = finder->first; 
			Poly pol(curVariable);
			lhs =  lhs + Rational(it->first) * pol;
		}
		lhs = lhs - Rational(c.getRHS());
		FormulaT subformulaA = FormulaT(lhs, c.getRelation());

		//Adding auxiliary constraint to ensure variables are assigned to 1 or 0.
		std::vector<carl::Variable> intVars;
		for(auto it = mVariablesCache.begin(); it != mVariablesCache.end(); it++){
			intVars.push_back(it->second);
		}
		FormulaT subformulaB = createAuxiliaryConstraint(intVars);
		FormulaT subformulaC = FormulaT(carl::FormulaType::AND, subformulaA, subformulaB);

		//Adding auxiliary constraint to interconnect the bool and int variables
		FormulaT subformulaD = interconnectVariables(mVariablesCache);

		FormulaT finalFormula = FormulaT(carl::FormulaType::AND, subformulaC, subformulaD);
		SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << finalFormula);
        return finalFormula;
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::createAuxiliaryConstraint(std::vector<carl::Variable>& vars){
		Poly pf(*vars.begin());
		FormulaT subformulaA = FormulaT(pf, carl::Relation::EQ);
		FormulaT subformulaB = FormulaT(pf - Rational(1), carl::Relation::EQ);
		FormulaT first = FormulaT(carl::FormulaType::XOR, subformulaA, subformulaB);
		if(vars.size() == 1){
			return first;
		}else{
			vars.erase(vars.begin());
			FormulaT f = FormulaT(carl::FormulaType::AND, first, createAuxiliaryConstraint(vars));
			return f;
		}
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::interconnectVariables(std::map<carl::Variable, carl::Variable>& vars){
		FormulasT newSubformulas;

		for(auto var : vars){
			FormulaT boolVar = FormulaT(var.first);
			Poly intVar(var.second);
			FormulaT subformulaA = FormulaT(intVar - Rational(1), carl::Relation::EQ);
			FormulaT subformulaB = FormulaT(carl::FormulaType::IMPLIES, boolVar, subformulaA);
			FormulaT subformulaC = FormulaT(intVar, carl::Relation::EQ);
			FormulaT subformulaD = FormulaT(carl::FormulaType::IMPLIES, boolVar.negated(), subformulaC);
			FormulaT newFormula  = FormulaT(carl::FormulaType::OR, subformulaB, subformulaD);
			newSubformulas.push_back(newFormula);
		}

		FormulaT result = FormulaT(carl::FormulaType::AND, std::move(newSubformulas));
		return result;
	}
}

#include "Instantiation.h"

