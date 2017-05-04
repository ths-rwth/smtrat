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
		checkFormulaTypeWithRNSFunction = std::bind(&PBPPModule<Settings>::checkFormulaTypeWithRNS, this, std::placeholders::_1);
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
		if(Settings::use_rns_transformation){
			FormulaT formula = mVisitor.visitResult(_subformula->formula(), checkFormulaTypeWithRNSFunction);
			addSubformulaToPassedFormula(formula, _subformula->formula());
			return true;
		}else{
			FormulaT formula = mVisitor.visitResult(_subformula->formula(), checkFormulaTypeFunction);
			addSubformulaToPassedFormula(formula, _subformula->formula());
			return true;
		}
		return true;
	}
	
	template<class Settings>
	void PBPPModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{	

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
		if(formula.getType() != carl::FormulaType::PBCONSTRAINT){
			return formula;
		} 

		const carl::PBConstraint& c = formula.pbConstraint();
		carl::Relation cRel = c.getRelation();
		const auto& cLHS = c.getLHS();
		auto cVars = c.gatherVariables();
		bool positive = true;
		bool negative = true;
		bool eqCoef = true;
		int cRHS = c.getRHS();
		int sum  = 0;
		int min = INT_MAX;
		int max = INT_MIN;
		int lhsSize = cLHS.size();

		for(auto it : cLHS){
			if(it.first < 0){
				positive = false;
			}else if(it.first > 0){
				negative = false;
			}

			if(it.first < min){
				min = it.first;
			}else if(it.first > max){
				max = it.first;
			}
			sum += it.first;
		}

		for(int i = 0; i < lhsSize - 1; i++){
			if(cLHS[i].first != cLHS[i + 1].first){
				eqCoef = false;
				break;
			}
		}

		//Filter out coefficients equal 0
		for(auto it : cLHS){	
			if(it.first == 0){
				return removeZeroCoefficients(formula);
			}
		}

		if(!positive && !negative){
			auto res = encodeMixedConstraints(formula);
			SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
			return res;
		}else if(eqCoef && (cLHS[0].first == 1 || cLHS[0].first == -1 ) && lhsSize > 1){
			auto res = encodeCardinalityConstratint(formula);
			SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
			return res;	
		}else if(lhsSize == 1){
			auto res = convertSmallFormula(formula);
			SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
			return res;
		}else if(!(positive && cRHS > 0 && sum > cRHS
			&& (cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER || cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS))
		&&  !(negative && cRHS < 0 && (cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER) && sum < cRHS)
		&& !(negative && cRHS < 0 && (cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS) && sum < cRHS)
		&& !((positive || negative) && cRel == carl::Relation::NEQ && sum != cRHS && cRHS != 0)
		&& !((positive || negative) && cRel == carl::Relation::NEQ && sum == cRHS && cRHS != 0)
		&& !(!positive && !negative)
		){
			auto res = convertBigFormula(formula);
			SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
			return res;
		}else{
			auto res = forwardAsArithmetic(formula);
			SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
			return res;
		}
	}


	template<typename Settings>
	FormulaT PBPPModule<Settings>::checkFormulaTypeWithRNS(const FormulaT& formula){
		if(formula.getType() != carl::FormulaType::PBCONSTRAINT){
			return formula;
		} 
		const carl::PBConstraint& c = formula.pbConstraint();
		carl::Relation cRel  = c.getRelation();
		const auto& cLHS	 = c.getLHS();
		bool positive = true;
		bool negative = true;
		int sum  = 0;
		bool eqCoef = true;


		for(auto it = cLHS.begin(); it != cLHS.end(); it++){
			sum += it->first;
			if(it->first < 0){
				positive = false;
			}else if(it->first > 0){
				negative = false;
			}
		}

		for(int i = 0; i < cLHS.size() - 1; i++){
			if(cLHS[i].first != cLHS[i + 1].first){
				eqCoef = false;
				break;
			}
		}

		//Filter out coefficients equal 0
		for(auto it : cLHS){	
			if(it.first == 0){
				return removeZeroCoefficients(formula);
			}
		}

		if(positive && !(eqCoef && cLHS[0].first == 1) && cRel == carl::Relation::EQ && cLHS.size() > 4){
			initPrimesTable();
			std::vector<carl::uint> base = calculateRNSBase(formula);
			if(base.size() != 0 && isNonRedundant(base, formula)){
				std::vector<FormulaT> subformulas;
				for(auto i : base){
					subformulas.push_back(rnsTransformation(formula, i));
				}
				auto res = FormulaT(carl::FormulaType::AND, std::move(subformulas));
				SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
				return res;
			}else{
<<<<<<< HEAD
				return checkFormulaType(formula);	
=======
				auto res = checkFormulaType(formula);
				SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
				return res;
>>>>>>> 0d5003e8aacc5d974bd6ef061f643e236289788e
			}
		}else{
			return checkFormulaType(formula);
		}		
	}


	template<typename Settings>
	FormulaT PBPPModule<Settings>::encodeMixedConstraints(const FormulaT& formula){
		const carl::PBConstraint& c = formula.pbConstraint();
		carl::Relation cRel = c.getRelation();
		const auto& cLHS = c.getLHS();
		auto cVars = c.gatherVariables();
		bool positive = true;
		bool negative = true;
		bool eqCoef = true;
		int cRHS = c.getRHS();
		int sum  = 0;
		int min = INT_MAX;
		int max = INT_MIN;
		int lhsSize = cLHS.size();

		for(auto it : cLHS){
			if(it.first < 0){
				positive = false;
			}else if(it.first > 0){
				negative = false;
			}

			if(it.first < min){
				min = it.first;
			}else if(it.first > max){
				max = it.first;
			}
			sum += it.first;
		}
		if(sum == 0 && cRel == carl::Relation::GEQ && cRHS == 0){
			int nsum = 0;
			int psum = 0;
			for(auto it : cLHS){
				if(it.first == 1){
					psum++;
				}else if(it.first == -1){
					nsum++;
				}
			}
			if(nsum == lhsSize - 1){
 				//-1 x1 -1x2 -1x3 -1x4 +4x5 >= 0 ===> not x1 or not x2 or not x3 or not x4 or x5
				int nsum = 0;
				int psum = 0;
				for(auto it : cLHS){
					if(it.first == 1){
						psum++;
					}else if(it.first == -1){
						nsum++;
					}
				}
				FormulasT subf;
				for(auto it : cLHS){
					if(it.first < 0){
						subf.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(it.second)));
					}else{
						subf.push_back(FormulaT(it.second));
					}
				}
				return FormulaT(carl::FormulaType::OR, std::move(subf));
			}else if(psum == lhsSize - 1){
				//1 x1 +1 x2 +1 x3 +1 x4 -4 x5 >= 0 ===> (x5 -> x1 and x2 and x3 and x4) or (x1 or x2 or x3 or x4)
				FormulaT subfA;
				FormulasT subfB;
				for(auto it : cLHS){
					if(it.first < 0){
						subfA = FormulaT(carl::FormulaType::NOT, FormulaT(it.second));
					}else{
						subfB.push_back(FormulaT(it.second));
					}
				}
				FormulaT subformulaB = FormulaT(carl::FormulaType::AND, std::move(subfB));
				FormulaT subformulaC = FormulaT(carl::FormulaType::OR, subfA, subformulaB); 
				FormulaT subformulaD = FormulaT(carl::FormulaType::OR, std::move(subfB));
				return FormulaT(carl::FormulaType::OR, subformulaD, subformulaC);
			}else{
				return forwardAsArithmetic(formula);
			}
		}else if(lhsSize == 2 && cRHS == max && sum == 0 && cRel == carl::Relation::GEQ){
			//-1 x1 +1 x2 >= 1 ===> not x1 and x2
			//std::cout << "HIER 2" << std::endl;
			FormulasT subf;
			for(auto it : cLHS){
				if(it.first < 0){
					subf.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(it.second)));
				}else{
					subf.push_back(FormulaT(it.second));
				}
			}
			return FormulaT(carl::FormulaType::AND, std::move(subf));
		}else if(lhsSize == 3 && sum == 1 && cRHS == 0 && cRel == carl::Relation::GEQ){
			//-1 x1 +1 x2 +1 x3 >= 0 ===> not x1 or x2 or x3
			//std::cout << "HIER 4" << std::endl;
			FormulasT subf;
			for(auto it : cLHS){
				if(it.first < 0){
					subf.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(it.second)));
				}else{
					subf.push_back(FormulaT(it.second));
				}
			}
			return FormulaT(carl::FormulaType::OR, std::move(subf));	
		}else if(cRel == carl::Relation::GEQ && sum == cRHS && cRHS < 0){
			//std::cout << "HERE" << std::endl;
			bool coef = true;
			int nsum = 0;
			for(auto it : cLHS){
				if((it.first != 1) && (it.first != -1)){
					return forwardAsArithmetic(formula);
				}else if(it.first == -1){
					nsum--;
				}
			}

			if(nsum == cRHS - 1){
				//+1 x1 -1 x2 -1 x3 -1 x4 -1x5 >= -3 ===> not(not x1 and x2 and x3 and x4 and x5)
				FormulasT subf;
				for(auto it : cLHS){
					if(it.first < 0){
						subf.push_back(FormulaT(it.second));
					}else{
						subf.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(it.second)));
					}
				}
				return FormulaT(carl::FormulaType::NOT, FormulaT(carl::FormulaType::AND, std::move(subf)));
			}else{
				return forwardAsArithmetic(formula);
			}
		}else{
			return forwardAsArithmetic(formula);
		}
	}


	template<typename Settings>
	FormulaT PBPPModule<Settings>::encodeCardinalityConstratint(const FormulaT& formula){
		const carl::PBConstraint& c = formula.pbConstraint();
		const auto& cLHS = c.getLHS();
		auto cVars = c.gatherVariables();
		int cRHS = c.getRHS();
		carl::Relation cRel = c.getRelation();
		int lhsSize = cLHS.size();
		int firstCoef = cLHS[0].first;
		int sum = 0;
		for(auto it : cLHS){
			sum += it.first;
		}

		if(cRel == carl::Relation::GEQ){
			if(firstCoef == -1 && cRHS == 1){
				//-1 x1 -1 x2 -1 x3 -1 x4 >= 1 ===> 
				//std::cout << "Card 1" << std::endl;

				//not x1 and not x2 and not x3 and not x4 ...
				FormulasT subformulasA;
				for(auto it : cVars){
					subformulasA.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(it)));
				}
				FormulaT subfA = FormulaT(carl::FormulaType::AND, std::move(subformulasA));

				//(x1 and not x2 and not x3 and not x4) or (not x1 and x2 and not x3 and not x4) or...
				FormulasT subformulasB;
				for(int i = 0; i < lhsSize -1; i++){
					FormulasT temp;
					temp.push_back(FormulaT(cVars[i]));
					for(int j = 0; j < lhsSize; j++){
						if(j != i){
							temp.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(cVars[j])));
						}
					}
					subformulasB.push_back(FormulaT(carl::FormulaType::AND, std::move(temp)));
				}
				FormulaT subfB = FormulaT(carl::FormulaType::OR, std::move(subformulasB));

				return FormulaT(carl::FormulaType::OR, subfA, subfB);
			}else if(firstCoef == 1 && cRHS == 1){
				//+1 x1 +1 x2 +1 x3 >= 1 ===> x1 or x2 or x3
				//std::cout << "Card 2" << std::endl;

				FormulasT subformulas;
				for(auto it : cVars){
					subformulas.push_back(FormulaT(it));
				}
				return FormulaT(carl::FormulaType::OR, std::move(subformulas));
			}else if(firstCoef == -1 && cRHS == -1){
				//-1 x1 -1 x2 -1 x3 -1 x4 >= -1 ===> (x1 and not x2 and not x3 and not x4) or (notx1 andx2 and not x3 and not x4) or ...
				//or (not x1 and not x2 and not x3 and not x4)

				FormulasT subformulasA;
				for(int i = 0; i < lhsSize; i++){
					FormulasT temp;
					temp.push_back(FormulaT(cVars[i]));
					for(int j = 0; j < lhsSize; j++){
						if(i != j){
							temp.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(cVars[j])));
						}
					}
					subformulasA.push_back(FormulaT(carl::FormulaType::AND, std::move(temp)));
				}
				FormulaT subformulaA = FormulaT(carl::FormulaType::OR, std::move(subformulasA));

				FormulasT subformulasB;
				for(auto it : cVars){
					subformulasB.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(it)));
				}
				FormulaT subformulaB = FormulaT(carl::FormulaType::AND, std::move(subformulasB));

				return FormulaT(carl::FormulaType::OR, subformulaA, subformulaB);
			}else if(lhsSize >= 2 && firstCoef == -1 && cRHS < 0 && cRHS > sum){
				//-1 x1 -1 x2 -1 x3 -1 x4 >= -2 ===> 
				//std::cout << "Card 3" << std::endl;

				FormulasT subsubformulas;
				for(int j = 0; j < (cRHS* -1); j++){
					std::vector<int> signs;
					for(int i = 0; i < lhsSize - (cRHS* -1) + j; i++){
						signs.push_back(-1);
					}
					for(int i = 0; i < (cRHS* -1) - j; i++){
						signs.push_back(1);
					}
					//std::cout << signs << std::endl;
					FormulasT subformulas;
					do{
						FormulasT temp;
						for(int i = 0; i < lhsSize; i++){
							if(signs[i] == -1){
								temp.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(cVars[i])));
							}else{
								temp.push_back(FormulaT(cVars[i]));
							}
						}
						subformulas.push_back(FormulaT(carl::FormulaType::AND, std::move(temp)));
						//std::cout << FormulaT(carl::FormulaType::AND, std::move(temp)) << std::endl;
					}while(std::next_permutation(signs.begin(), signs.end()));
					subsubformulas.push_back(FormulaT(carl::FormulaType::OR, std::move(subformulas)));
				}
				subsubformulas.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(generateVarChain(cVars, carl::FormulaType::OR))));
				return FormulaT(carl::FormulaType::OR, std::move(subsubformulas));		
			}else{
				return forwardAsArithmetic(formula);
			}		
		}else if(cRel == carl::Relation::EQ){
			if(cRHS > lhsSize && firstCoef == 1){
				//std::cout << "Card 4.1" << std::endl;
				return FormulaT(carl::FormulaType::FALSE);
			}else if(cRHS < lhsSize && firstCoef == -1){
				//std::cout << "Card 4.2" << std::endl;
				return FormulaT(carl::FormulaType::FALSE);
			}else if((firstCoef == 1 && cRHS < 0) || (firstCoef == -1 && cRHS > 0)){
				return FormulaT(carl::FormulaType::FALSE);
			}else if(firstCoef == 1 && cRHS == 0){
				//+1 x1 +1 x2 +1 x3 +1 x4 = 0  ===> not x1 and not x2 and not x3 and not x4
				FormulasT subformulas;
				for(auto it : cVars){
					subformulas.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(it)));
				}
				return FormulaT(carl::FormulaType::AND, std::move(subformulas));
			}else if(firstCoef == 1 && cRHS >= 1){
				//Calculate the signs = [-1, -1, -1, 1, 1] number of 1 is equal cRHS
				std::vector<int> sign;
				for(int i = 0; i < lhsSize - cRHS; i++){
					sign.push_back(-1);
				}
				for(int i = 0; i < cRHS; i++){
					sign.push_back(1);
				}
				FormulasT subformulasA;
				do{
					FormulasT temp;
					for(int i = 0; i < sign.size(); i++){
						if(sign[i] == 1){
							temp.push_back(FormulaT(cVars[i]));
						}else{
							temp.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(cVars[i]))); 
						}
					}
					subformulasA.push_back(FormulaT(carl::FormulaType::AND, std::move(temp)));
				}while(std::next_permutation(sign.begin(), sign.end()));
				FormulaT subformulaA = FormulaT(carl::FormulaType::OR, std::move(subformulasA));

				FormulasT subformulasB;
				for(int j = 1; j < cRHS; j++){
					//Calculate the signs = [-1, -1, -1, 1, 1] number of 1 is equal cRHS -j 
					std::vector<int> signs;
					for(int i = 0; i < lhsSize - cRHS + j; i++){
						signs.push_back(-1);
					}
					for(int i = 0; i < cRHS - j; i++){
						signs.push_back(1);
					}
					FormulasT subformulasC;
					do{
						FormulasT temp;
						for(int i = 0; i < signs.size(); i++){
							if(signs[i] == 1){
								temp.push_back(FormulaT(cVars[i]));
							}else{
								temp.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(cVars[i])));
							}
						}
						subformulasC.push_back(FormulaT(carl::FormulaType::AND, std::move(temp)));
					}while(std::next_permutation(signs.begin(), signs.end()));
					FormulaT subformulaC = FormulaT(carl::FormulaType::OR, std::move(subformulasC));
					subformulasB.push_back(FormulaT(carl::FormulaType::NOT, subformulaC));
				}
				FormulaT subformulaB = FormulaT(carl::FormulaType::AND, std::move(subformulasB));

				return FormulaT(carl::FormulaType::AND, subformulaA, subformulaB);
			}else{
				//+1 x1 +1 x2 +1 x3 +1 x4 = 3 ===> +1 x1 +1 x2 +1 x3 +1 x4 >= 3 and +1 x1 +1 x2 +1 x3 +1 x4 <= 3 
				carl::PBConstraint newConstA;
				carl::PBConstraint newConstB;

				newConstA.setLHS(cLHS);
				newConstA.setRelation(carl::Relation::GEQ);
				newConstA.setRHS(cRHS);
				FormulaT subformulaA = checkFormulaType(FormulaT(newConstA));

				newConstB.setLHS(cLHS);
				newConstB.setRelation(carl::Relation::LEQ);
				newConstB.setRHS(cRHS);
				FormulaT subformulaB = checkFormulaType(FormulaT(newConstB));

				return FormulaT(carl::FormulaType::AND, subformulaA, subformulaB);
			}
		}else{
			return forwardAsArithmetic(formula);
		}
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::removeZeroCoefficients(const FormulaT& formula){
		const carl::PBConstraint& c = formula.pbConstraint();
		const auto& cLHS = c.getLHS();
		int cRHS = c.getRHS();

		if(cLHS.size() == 1 && cRHS == 0){
			return FormulaT(carl::FormulaType::TRUE);
		}else if(cLHS.size() == 1 && cRHS != 0){
			return FormulaT(carl::FormulaType::FALSE);
		}

		carl::PBConstraint newConstr;
		std::vector<std::pair<int, carl::Variable>> newLHS;

		for(auto it : cLHS){
			if(it.first != 0){
				newLHS.push_back(std::pair<int, carl::Variable>(it.first, it.second));
			}
		}
		newConstr.setLHS(newLHS);
		newConstr.setRHS(cRHS);
		newConstr.setRelation(c.getRelation());

		return checkFormulaType(FormulaT(newConstr));

	}	


	template<typename Settings>
	FormulaT PBPPModule<Settings>::rnsTransformation(const FormulaT& formula, const carl::uint prime){
		const carl::PBConstraint& c = formula.pbConstraint();
		const auto& cLHS = c.getLHS();
		int cRHS = c.getRHS();
		std::vector<std::pair<int, carl::Variable>> newLHS;
		int newRHS = cRHS % (int) prime;
		carl::PBConstraint newConstraint;

		for(auto it : cLHS){
			int newCoeff = it.first % (int) prime;
			if(newCoeff != 0){
				newLHS.push_back(std::pair<int, carl::Variable>(newCoeff, it.second));
			}
		}
		
		if(newLHS.size() == 0 && newRHS > 0){
			return FormulaT(carl::FormulaType::FALSE);
		}else if(newLHS.size() == 0 && newRHS == 0){
			return FormulaT(carl::FormulaType::TRUE);
		}

		int t = 0;
		for(auto it : newLHS){
			t += it.first;
		}
		t = (int) std::floor((t - newRHS)/ (int) prime );

		for(int i = 0; i < t; i++){
			newLHS.push_back(std::pair<int, carl::Variable>(-t, carl::freshVariable(carl::VariableType::VT_BOOL)));
		}

		newConstraint.setLHS(newLHS);
		newConstraint.setRHS(newRHS);
		newConstraint.setRelation(carl::Relation::EQ);
		return checkFormulaType(FormulaT(newConstraint));		
	}


	template<typename Settings>
	FormulaT PBPPModule<Settings>::convertSmallFormula(const FormulaT& formula){
		//std::cout << "Convert small formula...";
		const carl::PBConstraint& c  = formula.pbConstraint();
		carl::Relation cRel = c.getRelation();
		const auto& cLHS = c.getLHS();
		int lhsCoeff = cLHS.begin()->first;
		FormulaT lhsVar = FormulaT(cLHS.begin()->second);
		int cRHS = c.getRHS();
		int lhsSize = cLHS.size();

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
		//std::cout << "OK" << std::endl;
		return formula;
	}


	template<typename Settings>
	FormulaT PBPPModule<Settings>::convertBigFormula(const FormulaT& formula){
		//std::cout << "Convert big formula...";
		const carl::PBConstraint& c = formula.pbConstraint();
		const auto& cLHS = c.getLHS();
		carl::Relation cRel = c.getRelation();
		auto cVars = c.gatherVariables();
		int cRHS = c.getRHS();
		bool positive = true;
		bool negative = true;
		bool eqCoef = true;
		int sum = 0;

		for(auto it : cLHS){
			if(it.first < 0){
				positive = false;
			}else if(it.first > 0){
				negative = false;
			}
			sum += it.first;
		}

		for(int i = 0; i < cLHS.size() - 1; i++){
			if(cLHS[i].first != cLHS[i + 1].first){
				eqCoef = false;
				break;
			}
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
				return generateVarChain(cVars, carl::FormulaType::AND);
			}else if(sum != cRHS && cRHS == 0){
				//5 x1 +2 x2 +3 x3 = 0 ===> (x1 or x2 or x3 -> false)
				FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::OR);
				FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
				return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
			}else{		
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
		//std::cout << "OK" << std::endl;
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
		//std::cout << "Forward as arithmetic..." << std::endl;
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
		auto boolVars = c.gatherVariables();
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
		//std::cout << "OK" << std::endl;
		return FormulaT(carl::FormulaType::AND, std::move(newSubformulas));
	}

	template<typename Settings>
	FormulaT PBPPModule<Settings>::interconnectVariables(const FormulaT& formula){
		const carl::PBConstraint& c = formula.pbConstraint();
		auto boolVars = c.gatherVariables();
		std::map<carl::Variable, carl::Variable> varsMap;

		for(auto var : boolVars){
			if(std::find(mConnectedVars.begin(), mConnectedVars.end(), var) == mConnectedVars.end()){
				//The variables are not interconnected
				varsMap.insert(*mVariablesCache.find(var));
				mConnectedVars.push_back(var);
			}
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
	std::vector<carl::uint> PBPPModule<Settings>::calculateRNSBase(const FormulaT& formula){
		const carl::PBConstraint& c = formula.pbConstraint();	
		const auto& cLHS = c.getLHS();
		std::vector<std::pair<int, carl::uint>> freq;
		carl::uint sum = 0;
		carl::uint product = 1;
		std::vector<carl::uint> base;

		for(auto it : cLHS){
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
					freq[(unsigned long) distance].first = freq[(unsigned long) distance].first + 1;
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

		for(int i = 0; i < base.size(); i++){
			if(base[i] == 1 || base[i] == 0){
				base.erase(base.begin() + i);
			} 
		}
		return base;
	}


    template<typename Settings>
	std::vector<carl::uint>PBPPModule<Settings>::integerFactorization(const int& coeff){ 
		if(coeff == 2){
			return std::vector<carl::uint>((carl::uint) 2);
		}else if(coeff <= 100){
			return mPrimesTable[(unsigned long) coeff];
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
					std::vector<carl::uint> v = mPrimesTable[(unsigned long) first];
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
					std::vector<carl::uint> v = mPrimesTable[(unsigned long) second];
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

		for(auto it : cLHS){
			if(it.first > max){
				max = it.first;
			}
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
