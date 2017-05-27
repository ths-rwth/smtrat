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
			const FormulaT& f = subformula.formula();
			if(f.getType() == carl::FormulaType::PBCONSTRAINT){
				const PBConstraintT& c = f.pbConstraint();
				c.collectVariables(mVariables);
				if(c.getRelation() == carl::Relation::EQ){
					mEquations.push_back(c);
				}else if(c.getRelation() == carl::Relation::LEQ || c.getRelation() == carl::Relation::GEQ
					|| c.getRelation() == carl::Relation::LESS || c.getRelation() == carl::Relation::GREATER){
					mInequalities.push_back(c);
				}else{
					addSubformulaToPassedFormula(f);
				}
			}else{
				addSubformulaToPassedFormula(f);
			}
		}
		
		FormulaT formula;
		if(mEquations.size() > 1){
			formula = gaussAlgorithm();

		}else{
			FormulasT subformulas;
			for(const auto& it : mInequalities){
				subformulas.push_back(FormulaT(it));
			}
			if(mEquations.size() == 1){
				subformulas.push_back(FormulaT(mEquations.front()));
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
		if(mEquations.size() == 0){
			return FormulaT(carl::FormulaType::TRUE);
		}else if(mEquations.size() == 1){
			return FormulaT(mEquations.front());
		}

		// Collect all variables
		carl::Variables eqVarSet;
		for(const auto& it : mEquations){
			it.collectVariables(eqVarSet);
		}
		std::vector<carl::Variable> eqVars(eqVarSet.begin(), eqVarSet.end());
		
		// Collect all coefficients and rhs
		std::vector<Rational> coef;
		for(const auto& it : mEquations){
			for(auto var : eqVars){
				coef.push_back(it.getCoefficient(var));
			}
			coef.push_back(it.getRHS());
		}
		
		std::size_t rows = mEquations.size();
		std::size_t columns = eqVars.size();

		MatrixT matrix = MatrixT::Map(coef.data(), columns + 1, rows).transpose();

		std::cout << "Matrix" << std::endl;
		for(auto i = 0; i < matrix.rows(); i++){
			VectorT r = matrix.row(i);
			std::vector<Rational> row(r.data(), r.data() + r.size());
			std::cout << row << std::endl;
		}

		//LU Decomposition
		Eigen::FullPivLU<MatrixT> lu(matrix);
		
		const MatrixT& u = lu.matrixLU().triangularView<Eigen::Upper>();
		const MatrixT& l = lu.matrixLU().triangularView<Eigen::StrictlyLower>();
		const MatrixT& q = lu.permutationQ();

		MatrixT newUpper = u * q.inverse();
		VectorT newB = newUpper.col(newUpper.cols() - 1);
		newUpper.conservativeResize(newUpper.rows(), newUpper.cols() - 1);

		std::cout << "Upper" << std::endl;
		for(auto i = 0; i < u.rows(); i++){
			VectorT r = u.row(i);
			std::vector<Rational> row(r.data(), r.data() + r.size());
			std::cout << row << std::endl;
		}

		std::cout << "newUpper" << std::endl;
		for(auto i = 0; i < newUpper.rows(); i++){
			VectorT r = newUpper.row(i);
			std::vector<Rational> row(r.data(), r.data() + r.size());
			std::cout << row << std::endl;
		}
		
		std::vector<carl::Relation> rels(newUpper.rows(), carl::Relation::EQ);
		if(mInequalities.size() == 0){
			return reconstructEqSystem(newUpper, eqVars, rels, newB);
		}else{
			return reduce(newUpper, newB, eqVarSet);
		}
	}

template<class Settings>
	FormulaT PBGaussModule<Settings>::reconstructEqSystem(const MatrixT& u, const std::vector<carl::Variable>& vars, const std::vector<carl::Relation>& rels,  const VectorT& b){
		FormulasT subformulas;
		for(long i = 0; i < u.rows(); i++){
			std::vector<std::pair<Rational, carl::Variable>> newLHS;
			const VectorT& r = u.row(i);
			
			// Compute least common multiple of all denominators
			Rational m = 1;
			for (long rid = 0; rid < r.size(); rid++) {
				if (!carl::isInteger(r[rid])){
					m = carl::lcm(m, carl::getDenom(r[rid]));
				}
			}
			// Restore 
			for(long j = 0; j < r.size(); j++){
				if (carl::isZero(r[j])) continue;
				newLHS.emplace_back(m * r[j], vars[j]);
			}
			subformulas.emplace_back(PBConstraintT(newLHS, rels[std::size_t(i)], b[i] * m));
		}

		return FormulaT(carl::FormulaType::AND, std::move(subformulas));
	}


template<class Settings>
	FormulaT PBGaussModule<Settings>::reduce(const MatrixT& u, const VectorT& b, const carl::Variables vars){

		std::vector<Rational> bVector(b.data(), b.data() + b.size());
		std::cout << "b" << std::endl;
		std::cout << bVector << std::endl;

		std::cout << mVariables << std::endl;
		//Resize u and add b
		std::vector<Rational> upperCoef;
		for(auto i = 0; i < u.rows(); i++){
			VectorT r = u.row(i);
			std::vector<Rational> row(r.data(), r.data() + r.size());
			for(auto j : mVariables){
				auto elem = vars.find(j);
				if(elem != vars.end()){
					upperCoef.push_back(row[std::distance(vars.begin(), elem)]);
				}else{
					upperCoef.push_back(0);
				}
			}
			upperCoef.push_back(bVector[i]);
		}

		std::cout << "upperCoef: " << upperCoef << std::endl;


		MatrixT uMatrix = MatrixT::Map(upperCoef.data(), mVariables.size() + 1, mEquations.size()).transpose();
		std::cout << "uMatrix" << std::endl;
		for(auto i = 0; i < uMatrix.rows(); i++){
			VectorT r = uMatrix.row(i);
			std::vector<Rational> row(r.data(), r.data() + r.size());
			std::cout << row << std::endl;
		}


		//Inequalities to matrix
		std::vector<carl::Relation> ineqRels;
		std::vector<Rational> ineqCoef;
		for(auto i : mInequalities){
			ineqRels.push_back(i.getRelation());
			auto iLHS = i.getLHS();
			for(auto j : mVariables){
				auto elem = std::find_if(iLHS.begin(), iLHS.end(), 
					[&] (const pair<Rational, carl::Variable>& elem){
						return elem.second == j;
					});
				if(elem != iLHS.end()){
					ineqCoef.push_back(elem->first);
				}else{
					ineqCoef.push_back(0);
				}
			}
			ineqCoef.push_back(i.getRHS());
		}


		MatrixT ineqMatrix = MatrixT::Map(ineqCoef.data(), mVariables.size() + 1, mInequalities.size()).transpose();
		std::cout << "ineqMatrix" << std::endl;
		for(auto i = 0; i < ineqMatrix.rows(); i++){
			VectorT r = ineqMatrix.row(i);
			std::vector<Rational> row(r.data(), r.data() + r.size());
			std::cout << row << std::endl;
		}





	}

// template<class Settings>
// 	FormulaT PBGaussModule<Settings>::reduce(const MatrixT& u){
// 		// Normalize the matrix, make diagonal entries one
// 		std::vector<Rational> newU;
// 		for (auto i = 0; i < u.rows(); i++) {
// 			for (long rid = 0; rid < u.row(i).size(); rid++) {
// 				newU.push_back(carl::div(u.row(i)[rid], u.row(i)[i]));
// 			}
// 		}


// 		MatrixT newUpper = MatrixT::Map(newU.data(), u.cols(), u.rows()).transpose();

// 		// std::cout << "newUpper" << std::endl;
// 		// for(auto i = 0; i < newUpper.rows(); i++){
// 		// 	VectorT r = newUpper.row(i);
// 		// 	std::vector<Rational> row(r.data(), r.data() + r.size());
// 		// 	std::cout << row << std::endl;
// 		// }

// 		std::vector<Rational> rhs;
// 		std::vector<carl::Relation> ineqRels;
// 		carl::Variables ineqVarSet;
// 		for(const auto& it : inequalities){
// 			//TODO: Die Variablenreihenfolge ist *vermutlich* identisch wie in gaussAlgorithm(), wahrscheinlich aber eher nicht.
// 			// Da das aber essentiell ist, damit das hier alles funktioniert, würde ich die einmal explizit in checkCore bestimmen und in einem Member speichern.
// 			// Ich habe das mit collectVariables() nun erstmal in ein std::set geschrieben, d.h. die sind sortiert, aber eventuell kommt eine Variable nur in equalities vor, nicht aber in inequalities. Und dann wäre alles kaputt...
// 			it.collectVariables(ineqVarSet);
// 			rhs.push_back(it.getRHS());
// 			carl::Relation rel = it.getRelation();
// 			if(rel == carl::Relation::LESS){
// 				rel = carl::Relation::LEQ;
// 			}else if(rel == carl::Relation::GREATER){
// 				rel = carl::Relation::GEQ;
// 			}
// 			ineqRels.push_back(rel);
// 		}
// 		std::vector<carl::Variable> ineqVars(ineqVarSet.begin(), ineqVarSet.end());
		

// 		//inequalities to Matrix
// 		std::vector<Rational> coef; 
// 		for(auto it : inequalities){
// 			for (auto var : ineqVars){
// 				coef.push_back(it.getCoefficient(var));
// 			}
// 			coef.push_back(it.getRHS());
// 		}

// 		// //TODO: Könnte man rhs nicht direkt in coef mit reinschreiben, statt diesen Umweg?
// 		// MatrixT ineqMatrix = MatrixT::Map(coef.data(), (long) ineqVars.size(), (long) inequalities.size()).transpose();
// 		// VectorT b = VectorT::Map(rhs.data(), (long) rhs.size());
// 		// MatrixT temp(ineqMatrix.rows(), ineqMatrix.cols() + 1);
// 		// temp << ineqMatrix, b;
// 		// ineqMatrix = temp;
// 		MatrixT ineqMatrix = MatrixT::Map(coef.data(), (long) ineqVars.size(), (long) inequalities.size() + 1).transpose();

// 		//Combine
// 		MatrixT result(ineqVars.size() + 1, 0);
// 		for(auto i = 0; i < ineqMatrix.rows();){
// 			const VectorT& row = ineqMatrix.row(i);

// 			//Is it possible to simplify?
// 			Rational m;
// 			long column = -1;
// 			for(auto j = 0; j < row.size(); j++){
// 				if(row(j) != 0){
// 					m = row(j);
// 					column = j;
// 					break;
// 				}
// 			}
// 			assert(column != -1);

// 			if(column >= 0 && column < newUpper.rows()){
// 				//Reduce
// 				VectorT eqRow = newUpper.row(column);
// 				conservativeResize(eqRow, row.size());
// 				//TODO: Ich glaube hier wird rhs nicht korrekt behandelt.
// 				ineqMatrix.row(i) = (-m * eqRow) + row;  
// 				//Update relation
// 				if(inequalities[(std::size_t) i].getRelation() == carl::Relation::LESS){
// 					ineqRels[(std::size_t) i] = carl::Relation::LEQ;
// 				}else if(inequalities[(std::size_t) i].getRelation() == carl::Relation::GREATER){
// 					ineqRels[(std::size_t) i] = carl::Relation::GEQ;
// 				}
// 				// Try again with this (simplified) row
// 				continue;
// 			} else {
// 				//It is not possible to simplify.
// 				result.conservativeResize(result.rows(), result.cols() + 1);
// 				result.col(result.cols()-1) = ineqMatrix.row(i);
// 				// Go to next row
// 				i++;
// 			}
// 		}
		
// 		for (const auto& it: equations) {
// 			addSubformulaToPassedFormula(FormulaT(it));
// 		}
		
// 		MatrixT resultT = result.transpose();
// 		const VectorT& newB = resultT.col(resultT.cols() - 1);
// 		resultT.conservativeResize(resultT.rows(), resultT.cols() - 1);
// 		return  reconstructEqSystem(resultT, ineqVars, ineqRels, newB);

// 	}	

}

#include "Instantiation.h"
