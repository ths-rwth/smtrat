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
			getBackendsModel();
		}
	}
	
	template<class Settings>
	Answer PBGaussModule<Settings>::checkCore()
	{
		for(const auto& subformula : rReceivedFormula()){
			FormulaT f = subformula.formula();
			if(f.getType() == carl::FormulaType::PBCONSTRAINT){
				const PBConstraintT& c = f.pbConstraint();
				if(c.getRelation() == carl::Relation::EQ){
					equations.push_back(c);
				}else if(c.getRelation() == carl::Relation::LEQ || c.getRelation() == carl::Relation::GEQ
					|| c.getRelation() == carl::Relation::LESS || c.getRelation() == carl::Relation::GREATER){
					inequalities.push_back(c);
				}else{
					addSubformulaToPassedFormula(f);
				}
			}else{
				addSubformulaToPassedFormula(f);
			}
		}
	
		// FormulaT subfA = gaussAlgorithm();
		// FormulasT subf;
		// for(auto it : inequalities){
		// 	subf.push_back((FormulaT) it);
		// }	
		// FormulaT subfB = FormulaT(carl::FormulaType::AND, std::move(subf));
		// FormulaT formula = FormulaT(carl::FormulaType::AND, subfA, subfB);
		FormulaT formula = gaussAlgorithm();
		addSubformulaToPassedFormula(formula);
		Answer answer = runBackends();
		if (answer == Answer::UNSAT) {
			generateTrivialInfeasibleSubset();
		}
		return answer;
	}


	template<class Settings>
	FormulaT PBGaussModule<Settings>::gaussAlgorithm(){
		// std::cout << "Gauss" << std::endl;
		if(equations.size() == 0){
			return FormulaT(carl::FormulaType::TRUE);
		}else if(equations.size() == 1){
			return (FormulaT) *(equations.begin()); 
		}

		const long rows = (const long) equations.size();
		std::vector<Rational> rhs;

		for(const auto& it : equations){
			for(const auto& i : it.getLHS()){
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
				
		const long columns = (const long) vars.size();

		MatrixT matrix;
		int counter = 0;
		std::vector<Rational> coef;
		for(auto it : equations){
			auto lhs = it.getLHS();
			auto lhsVars = it.gatherVariables();
			
			for(auto i : vars){
				if(std::find(lhsVars.begin(), lhsVars.end(), i) == lhsVars.end()){
					//Variable is not in the equation ==> coeff must be 0
					coef.push_back(0);
				}else{
					auto elem = std::find_if(lhs.begin(), lhs.end(), 
					[&] (const pair<Rational, carl::Variable>& elem){
						return elem.second == i;
					});
					coef.push_back(elem->first);
				}
				counter++;
			}
		}

		matrix = MatrixT::Map(&coef[0], columns, rows).transpose();
		VectorT b = VectorT::Map(&rhs[0], (long) rhs.size());

		// std::cout << "Matrix:" << std::endl;
		// for(auto i = 0; i < matrix.rows(); i++){
		// 	VectorT r = matrix.row(i);
		// 	std::vector<Rational> row(r.data(), r.data() + r.size());
		// 	std::cout << row << std::endl;
		// }


		// std::cout << "matrix:" << matrix.rows() << ", " << matrix.cols() << std::endl;
		//Add b to matrix
		MatrixT temp(matrix.rows(), matrix.cols() + 1);
		temp << matrix, b; 
		matrix = temp;
		// std::cout << "matrix:" << matrix.rows() << ", " << matrix.cols() << std::endl;

		// std::cout << "Matrix:" << std::endl;
		// for(auto i = 0; i < matrix.rows(); i++){
		// 	VectorT r = matrix.row(i);
		// 	std::vector<Rational> row(r.data(), r.data() + r.size());
		// 	std::cout << row << std::endl;
		// }



		//LU Decomposition

		Eigen::FullPivLU<MatrixT> lu(matrix);
		VectorT newB;
		MatrixT newUpper;
		
		MatrixT u = lu.matrixLU().triangularView<Eigen::Upper>();
		MatrixT l = lu.matrixLU().triangularView<Eigen::StrictlyLower>();
		MatrixT p = lu.permutationP();
		MatrixT q = lu.permutationQ();

		newUpper = u * q.inverse();
		newB = newUpper.col(newUpper.cols() - 1);
		newUpper.conservativeResize(newUpper.rows(), newUpper.cols() - 1);



		
		// std::cout << "Upper:" << std::endl;
		// for(auto i = 0; i < newUpper.rows(); i++){
		// 	VectorT r = newUpper.row(i);
		// 	std::vector<Rational> row(r.data(), r.data() + r.size());
		// 	std::cout << row << std::endl;
		// }

		
		// std::cout << "Lower:" << std::endl;
		// for(auto i = 0; i < l.rows(); i++){
		// 	VectorT r = l.row(i);
		// 	std::vector<Rational> row(r.data(), r.data() + r.size());
		// 	std::cout << row << std::endl;
		// }

		// std::cout << "b:" << std::endl;
		// 	std::vector<Rational> row(newB.data(), newB.data() + newB.size());
		// 	std::cout << row << std::endl;
		
		std::vector<carl::Relation> rels;
		for(auto i = 0; i < newUpper.rows(); i++){
			rels.push_back(carl::Relation::EQ);
		}
		if(inequalities.size() == 0){
			return reconstructEqSystem(newUpper, rels, newB);
		}else{
			return reduce(u);
		}
	}

template<class Settings>
FormulaT PBGaussModule<Settings>::reconstructEqSystem(const MatrixT& u, const std::vector<carl::Relation>& rels,  const VectorT& b){
	// std::cout << "reconstruct" << std::endl;
    FormulasT subformulas;
    const MatrixT temp = u;

	// std::cout << "Upper:" << std::endl;
	// 	for(auto i = 0; i < temp.rows(); i++){
	// 		VectorT r = temp.row(i);
	// 		std::vector<Rational> row(r.data(), r.data() + r.size());
	// 		std::cout << row << std::endl;
	// 	}

    for(long i = 0; i < temp.rows(); i++){
    	std::vector<std::pair<Rational, carl::Variable>> newLHS;
    	VectorT r = temp.row(i);
    	std::vector<Rational> row(r.data(), r.data() + r.size());
    	// std::cout << "row: " << row << std::endl;
    	Rational m = 1;
    	for(auto it : row){
    		if(!carl::isInteger(it)){
    			m *= carl::getDenom(it);
    		}
    	}
    	for(std::size_t j = 0; j < row.size(); j++){
    		Rational currCoef = row[j];
    		carl::Variable currVar = vars[j];
    		newLHS.push_back(std::pair<Rational, carl::Variable>(m * currCoef, currVar));
    	}
    	// std::cout << (FormulaT) PBConstraintT(newLHS, carl::Relation::EQ, b[(long)i] * m) << std::endl;
    	subformulas.push_back((FormulaT) PBConstraintT(newLHS, rels[(std::size_t)i], b[(long)i] * m));
    }

    return FormulaT(carl::FormulaType::AND, std::move(subformulas));
}




	template<class Settings>
	FormulaT PBGaussModule<Settings>::reduce(const MatrixT& u){
		std::cout << "Upper:" << std::endl;
		for(auto i = 0; i < u.rows(); i++){
			VectorT r = u.row(i);
			std::vector<Rational> row(r.data(), r.data() + r.size());
			std::cout << row << std::endl;
		}

		//Normalize the matrix
		std::vector<Rational> newU;
		for(auto i = 0; i < u.rows(); i++){
			VectorT r = u.row(i);
			std::vector<Rational> row(r.data(), r.data() + r.size());
			Rational div = row[(std::size_t)i];
			for(auto i : row){
				newU.push_back(carl::div(i, div));
			}
		}

		MatrixT newUpper(u.rows(), u.cols());
		newUpper = MatrixT::Map(&newU[0], u.cols(), u.rows()).transpose();
		std::cout << "Upper:" << std::endl;
		for(auto i = 0; i < newUpper.rows(); i++){
			VectorT r = newUpper.row(i);
			std::vector<Rational> row(r.data(), r.data() + r.size());
			std::cout << row << std::endl;
		}



		//inequalities to Matrix
		MatrixT ineqMatrix;
		int counter = 0;
		std::vector<Rational> coef;
		std::vector<Rational> rhs;
		std::vector<carl::Relation> rels;
		for(auto it : inequalities){
			auto lhs = it.getLHS();
			auto lhsVars = it.gatherVariables();
			auto rel = it.getRelation();
			if(rel == carl::Relation::LESS){
				rel = carl::Relation::LEQ;
			}else if(rel == carl::Relation::GREATER){
				rel = carl::Relation::GEQ;
			}
			rels.push_back(rel);
			rhs.push_back(it.getRHS());
			for(auto i : vars){
				if(std::find(lhsVars.begin(), lhsVars.end(), i) == lhsVars.end()){
					//Variable is not in the inequality ==> coeff must be 0
					coef.push_back(0);
				}else{
					auto elem = std::find_if(lhs.begin(), lhs.end(), 
					[&] (const pair<Rational, carl::Variable>& elem){
						return elem.second == i;
					});
					coef.push_back(elem->first);
				}
				counter++;
			}
		}

		ineqMatrix = MatrixT::Map(&coef[0], (long) vars.size(), (long) inequalities.size()).transpose();
		VectorT b = VectorT::Map(&rhs[0], (long) rhs.size());
		MatrixT temp(ineqMatrix.rows(), ineqMatrix.cols() + 1);
		temp << ineqMatrix, b; 
		ineqMatrix = temp;

		std::cout << "ineqMatrix:" << std::endl;
		for(auto i = 0; i < ineqMatrix.rows(); i++){
			VectorT r = ineqMatrix.row(i);
			std::vector<Rational> row(r.data(), r.data() + r.size());
			std::cout << row << std::endl;
		}

		//Combine
		
		MatrixT result(vars.size() + 1, 1);
		for(auto i = 0; i < ineqMatrix.rows(); i++){
			VectorT r = ineqMatrix.row(i);
			std::vector<Rational> row(r.data(), r.data() + r.size());
		
			//Is it possible to simplify?
			std::size_t j = 0;
			Rational multiplier = 1;
			for(; j < row.size(); j++){
				if(row[j] != 0){
					multiplier = row[j];
					break;
				} 
			}
			if((long) j <= newUpper.rows()){
				VectorT tmp = newUpper.row((long) j);
				std::vector<Rational> tmpVector(tmp.data(), tmp.data() + tmp.size());
				//Add
				tmp *= -multiplier;
				VectorT newVector = tmp + r;
				result.conservativeResize(result.rows(), result.cols() + 1);
				result.col(result.cols() - 1) = newVector;		
			}else{
				result.conservativeResize(result.rows(), result.cols() + 1);
				result.row(result.cols()-1) = r;
			}
		}

		MatrixT resultT = result.transpose();
		std::cout << "result:" << std::endl;
		for(auto i = 0; i < resultT.rows(); i++){
			VectorT r = resultT.row(i);
			std::vector<Rational> row(r.data(), r.data() + r.size());
			std::cout << row << std::endl;
		}

		VectorT newB = resultT.col(resultT.cols() - 1);
		resultT.conservativeResize(resultT.rows(), resultT.cols() - 1);
		return  reconstructEqSystem(resultT, rels, newB);

	}

}

#include "Instantiation.h"
