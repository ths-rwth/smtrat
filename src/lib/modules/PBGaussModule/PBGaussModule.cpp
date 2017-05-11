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
		std::vector<double> rhs;

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
			rhs.push_back(it.getRHS());
		}

		
		const int columns = vars.size();

		Eigen::MatrixXd matrix;
		int counter = 0;
		std::vector<double> coef;
		for(auto it : equations){
			auto lhs = it.getLHS();
			auto lhsVars = it.gatherVariables();
			
			for(auto i : vars){
				if(std::find(lhsVars.begin(), lhsVars.end(), i) == lhsVars.end()){
					//Variable is not in the equation ==> coeff must be 0
					coef.push_back(0.0);
				}else{
					auto elem = std::find_if(lhs.begin(), lhs.end(), 
					[&] (const pair<int, carl::Variable>& elem){
						return elem.second == i;
					});
					coef.push_back((double) elem->first);
				}
				counter++;
			}
		}
		matrix = Eigen::MatrixXd::Map(&coef[0], columns, rows).transpose();
		Eigen::VectorXd b = Eigen::VectorXd::Map(&rhs[0], rhs.size());



		int dim;
		if(rows < columns){
			dim = columns;
			Eigen::MatrixXd id(dim, dim);
			Eigen::MatrixXd::Identity(columns,dim);            
			id.setIdentity(columns,dim);
			Eigen::MatrixXd newMatrix(columns, columns);
			id << matrix;
			matrix = id;

			Eigen::VectorXd temp = Eigen::VectorXd::Zero(dim);
			temp << b;
			b = temp;

		}else{
			dim = rows;
		}

		std::cout << "Matrix:" << std::endl;
		std::cout << matrix << std::endl;

		std::cout << "b:" << std::endl;
		std::cout << b << std::endl;


		//LU Decomposition

		Eigen::FullPivLU<Eigen::Matrix<double, Eigen::Dynamic, Eigen::Dynamic>> lu(matrix);
		Eigen::MatrixXd u(rows, columns);
		Eigen::MatrixXd p(rows, columns);
		Eigen::MatrixXd q(rows, columns);
		Eigen::VectorXd newB;
		Eigen::MatrixXd newUpper;

		u = lu.matrixLU().triangularView<Eigen::Upper>();
		p = lu.permutationP();
		q = lu.permutationQ();
		newB = p * b;
		newUpper = u * q.inverse();

		// Eigen::MatrixXd l(dim, dim);
		// Eigen::MatrixXd::Identity(dim,dim);            
		// l.setIdentity(dim,dim);
		// l.triangularView<Eigen::StrictlyLower>() = lu.matrixLU();

		// std::cout << "upper:" << std::endl;
		// std::cout << u << std::endl;
		// std::cout << "permutation P:" << std::endl;
		// std::cout << p << std::endl;
		// std::cout << "permutation Q:" << std::endl;
		// std::cout << q << std::endl;
		// std::cout << "Let us now reconstruct the original matrix m:" << std::endl;
		// std::cout << lu.permutationP().inverse() * l * u * lu.permutationQ().inverse() << std::endl;
		// std::cout << "newB:" << std::endl;
		// std::cout << newB << std::endl;
		// std::cout << "newUpper:" << std::endl;
		// std::cout << newUpper << std::endl;

	}

	template<class Settings>
	FormulaT PBGaussModule<Settings>::forwardInequalities(){
		return FormulaT(carl::FormulaType::TRUE);
	}

}

#include "Instantiation.h"
