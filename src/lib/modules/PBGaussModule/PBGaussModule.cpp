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
	bool PBGaussModule<Settings>::informCore( const FormulaT& )
	{

		return true;
	}
	
	template<class Settings>
	void PBGaussModule<Settings>::init()
	{}
	
	template<class Settings>
	bool PBGaussModule<Settings>::addCore( ModuleInput::const_iterator )
	{
		return true;
	}
	
	template<class Settings>
	void PBGaussModule<Settings>::removeCore( ModuleInput::const_iterator )
	{}
	
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

		FormulaT formula;
		if(equations.size() > 1){
			formula = gaussAlgorithm();

		}else{
			FormulasT subformulas;
			for(auto it : inequalities){
				subformulas.push_back((FormulaT) it);
			}
			if(equations.size() == 1){
				subformulas.push_back((FormulaT) *equations.begin());
			}
			formula = FormulaT(carl::FormulaType::AND, std::move(subformulas));
		}
		
		addSubformulaToPassedFormula(formula);
		Answer answer = runBackends();
		if (answer == Answer::UNSAT) {
			generateTrivialInfeasibleSubset();
		}
		return answer;
	}


	template<class Settings>
	FormulaT PBGaussModule<Settings>::gaussAlgorithm(){
		if(equations.size() == 0){
			return FormulaT(carl::FormulaType::TRUE);
		}else if(equations.size() == 1){
			return (FormulaT) *(equations.begin()); 
		}

		const long rows = (const long) equations.size();
		std::vector<Rational> rhs;
		std::vector<carl::Variable> eqVars;

		for(const auto& it : equations){
			for(const auto& i : it.getLHS()){
				auto elem = std::find_if(eqVars.begin(), eqVars.end(), 
					[&] (const carl::Variable& elem){
						return elem.getName() == i.second.getName();
					});
				if(elem == eqVars.end()){
					//The variable is not in the list
					eqVars.push_back(i.second);
				}
			}
			rhs.push_back(it.getRHS());
		}

		const long columns = (const long) eqVars.size();

		MatrixT matrix;
		int counter = 0;
		std::vector<Rational> coef;
		for(auto it : equations){
			auto lhs = it.getLHS();
			auto lhsVars = it.gatherVariables();
			
			for(auto i : eqVars){
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
		//Add b to matrix
		MatrixT temp(matrix.rows(), matrix.cols() + 1);
		temp << matrix, b; 
		matrix = temp;

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
		std::vector<carl::Relation> rels;
		for(auto i = 0; i < newUpper.rows(); i++){
			rels.push_back(carl::Relation::EQ);
		}
		if(inequalities.size() == 0){
			return reconstructEqSystem(newUpper, eqVars, rels, newB);
		}else{
			return reduce(u);
		}
	}

template<class Settings>
	FormulaT PBGaussModule<Settings>::reconstructEqSystem(const MatrixT& u, const std::vector<carl::Variable>& vars, const std::vector<carl::Relation>& rels,  const VectorT& b){
		FormulasT subformulas;
		const MatrixT temp = u;
		for(long i = 0; i < temp.rows(); i++){
			std::vector<std::pair<Rational, carl::Variable>> newLHS;
			VectorT r = temp.row(i);
			std::vector<Rational> row(r.data(), r.data() + r.size());
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
			subformulas.push_back((FormulaT) PBConstraintT(newLHS, rels[(std::size_t)i], b[(long)i] * m));
		}

		return FormulaT(carl::FormulaType::AND, std::move(subformulas));
	}

template<class Settings>
	FormulaT PBGaussModule<Settings>::reduce(const MatrixT& u){
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
		std::vector<carl::Variable> ineqVars;
		std::vector<Rational> rhs;
		std::vector<carl::Relation> ineqRels;
		for(const auto& it : inequalities){
			for(const auto& i : it.getLHS()){
				auto elem = std::find_if(ineqVars.begin(), ineqVars.end(), 
					[&] (const carl::Variable& elem){
						return elem.getName() == i.second.getName();
					});
				if(elem == ineqVars.end()){
					//The variable is not in the list
					ineqVars.push_back(i.second);
				}
			}
			rhs.push_back(it.getRHS());
			carl::Relation rel = it.getRelation();
			if(rel == carl::Relation::LESS){
				rel = carl::Relation::LEQ;
			}else if(rel == carl::Relation::GREATER){
				rel = carl::Relation::GEQ;
			}
			ineqRels.push_back(rel);
		}

    //inequalities to Matrix
		MatrixT ineqMatrix;
		int counter = 0;
		std::vector<Rational> coef; 
		for(auto it : inequalities){
			auto lhs = it.getLHS();
			auto lhsVars = it.gatherVariables();
			for(auto i : ineqVars){
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

		ineqMatrix = MatrixT::Map(&coef[0], (long) ineqVars.size(), (long) inequalities.size()).transpose();
		VectorT b = VectorT::Map(&rhs[0], (long) rhs.size());
		MatrixT temp(ineqMatrix.rows(), ineqMatrix.cols() + 1);
		temp << ineqMatrix, b;
		ineqMatrix = temp;

    	//Combine
		std::vector<PBConstraintT> usedEq;
		MatrixT result(ineqVars.size() + 1, 0);
		for(auto i = 0; i < ineqMatrix.rows(); i++){
			VectorT row = ineqMatrix.row(i);

    	//Is it possible to simplify?
			Rational m;
			long column = 0;
			for(auto j = 0; j < row.size(); j++){
				if(ineqMatrix(i,j) != 0){
					m = ineqMatrix(i,j);
					break;
				}
				column++;
			}

			if(column < newUpper.rows()){
    		//Reduce
				VectorT eqRow = newUpper.row(column);
				eqRow.conservativeResize(eqRow.size() + (row.size() - eqRow.size()));
				VectorT newVector = (-m * eqRow) + row;
				ineqMatrix.row(i) = newVector;  
            //Update relation
				if(inequalities[(std::size_t) i].getRelation() == carl::Relation::LESS){
					ineqRels[(std::size_t) i] = carl::Relation::LEQ;
				}else if(inequalities[(std::size_t) i].getRelation() == carl::Relation::GREATER){
					ineqRels[(std::size_t) i] = carl::Relation::GEQ;
				}
			}else{
    		//It is not possible to simplify.
				result.conservativeResize(result.rows(), result.cols() + 1);
				result.col(result.cols()-1) = row;
			}



		}

		if(usedEq.size() != equations.size()){
        //Add unused equations
			for(auto it : equations){
				auto elem = std::find_if(usedEq.begin(), usedEq.end(), 
					[&] (const PBConstraintT& elem){
						return elem == it;
					});
				if(elem == usedEq.end()){
                //The eq has not been used 
					addSubformulaToPassedFormula((FormulaT) it);
				}
			}

		}
		MatrixT resultT = result.transpose();
		VectorT newB = resultT.col(resultT.cols() - 1);
		resultT.conservativeResize(resultT.rows(), resultT.cols() - 1);
		return  reconstructEqSystem(resultT, ineqVars, ineqRels, newB);

	}	

}

#include "Instantiation.h"
