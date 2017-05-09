/**
 * @file PBGauss.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2017-05-03
 * Created on 2017-05-03.
 */

#include "PBGaussModule.h"

namespace smtrat
{
	template<class Settings>
	PBGaussModule<Settings>::PBGaussModule(const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager )
#ifdef SMTRAT_DEVOPTION_Statistics
		, mStatistics(Settings::moduleName)
#endif
	{}
	
	template<class Settings>
	PBGaussModule<Settings>::~PBGaussModule()
	{}
	
	template<class Settings>
	bool PBGaussModule<Settings>::informCore( const FormulaT& _constraint )
	{

		return true;
	}
	
	template<class Settings>
	void PBGaussModule<Settings>::init()
	{}
	
	template<class Settings>
	bool PBGaussModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		FormulaT f;
		for( const auto& subformula: rReceivedFormula()){
			f = subformula.formula();
			const carl::PBConstraint& c = f.pbConstraint();
			if(c.getRelation() == carl::Relation::EQ){
				equations.push_back(c);
			}else{
				inequalities.push_back(c);
			}
		}
		FormulaT subfA = FormulaT(carl::FormulaType::TRUE);
		FormulaT subfB = FormulaT(carl::FormulaType::TRUE);
		if(equations.size() != 0){
			subfA = gaussAlgorithm();

		}else if(inequalities.size() != 0){
			subfB = forwardInequalities();
		}
		FormulaT formula = FormulaT(carl::FormulaType::AND, subfA, subfB);
		addSubformulaToPassedFormula(formula, _subformula->formula());
		return true;
	}
	
	template<class Settings>
	void PBGaussModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		
	}
	
	template<class Settings>
	void PBGaussModule<Settings>::updateModel() const
	{
		mModel.clear();
		if( solverState() == Answer::SAT )
		{
			
		}
	}
	
	template<class Settings>
	Answer PBGaussModule<Settings>::checkCore()
	{
		
		return Answer::UNKNOWN; 
	}

	template<class Settings>
	FormulaT PBGaussModule<Settings>::gaussAlgorithm(){
		const int rows = equations.size();

		for(auto it : equations){
			for(auto i : it.getLHS()){
				auto elem = std::find_if(vars.begin(), vars.end(), 
					[&] (const carl::Variable& elem){
						return elem.getName() == i.second.getName();
					});
				if(elem == vars.end()){
					//The variable is not in the list
					vars.push_back(i.second);
				}
			}
		}

		
		const int columns = vars.size();

		Eigen::MatrixXi matrix;
		int counter = 0;
		std::vector<int> coef;
		for(auto it : equations){
			auto lhs = it.getLHS();
			auto lhsVars = it.gatherVariables();
			
			for(auto i : vars){
				if(std::find(lhsVars.begin(), lhsVars.end(), i) == lhsVars.end()){
					//Variable is not in the equation ==> coeff must be 0
					coef.push_back(0);
				}else{
					auto elem = std::find_if(lhs.begin(), lhs.end(), 
					[&] (const pair<int, carl::Variable>& elem){
						return elem.second == i;
					});
					coef.push_back(elem->first);
				}
				counter++;
			}
		}
		matrix = Eigen::MatrixXi::Map(&coef[0], columns, rows).transpose();
		//LU Decomposition
		Eigen::MatrixXi a(rows, columns);
		a = matrix;
		Eigen::FullPivLU<Eigen::Matrix<int, rows, columns>> lu(a);
		int dim = 0;

		Eigen::MatrixXi u(rows, columns);
		u = lu.matrixLU().triangularView<Eigen::Upper>();

		std::cout << "upper:" << std::endl;
		std::cout << u << std::endl;
	}

	template<class Settings>
	FormulaT PBGaussModule<Settings>::forwardInequalities(){
		return FormulaT(carl::FormulaType::TRUE);
	}

	template<class Settings>
	std::vector<int> PBGaussModule<Settings>::multiplyRow(int row){

	}

	template<class Settings>
	std::vector<int> PBGaussModule<Settings>::addTwoRows(int rowA, int rowB){

	}

	template<class Settings>
	std::vector<int> PBGaussModule<Settings>::swapRows(int rowA, int rowB){

	}
}

#include "Instantiation.h"
