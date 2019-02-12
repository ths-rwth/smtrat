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
	PBGaussModule<Settings>::PBGaussModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager):
	Module( _formula, _conditionals, _manager )
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
			if(f.getType() == carl::FormulaType::CONSTRAINT){
				const ConstraintT& c = f.constraint();
				for (const auto& var : c.variables()) {
					mVariables.insert(var);
				}

				if(c.relation() == carl::Relation::EQ){
					mEquations.push_back(c);
				}else if(c.relation() == carl::Relation::LEQ || c.relation() == carl::Relation::GEQ
					|| c.relation() == carl::Relation::LESS || c.relation() == carl::Relation::GREATER){
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
			SMTRAT_LOG_DEBUG("smtrat.gauss", "Gaussing resulted in " << formula);
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
		SMTRAT_LOG_DEBUG("smtrat.gauss", "Gaussing " << mEquations);
		if(mEquations.size() == 0){
			return FormulaT(carl::FormulaType::TRUE);
		}else if(mEquations.size() == 1){
			return FormulaT(mEquations.front());
		}

		// Collect all variables
		carl::Variables eqVarSet;
		for(const auto& it : mEquations){
			for (const auto& var : it.variables()) {
				eqVarSet.insert(var);
			}
		}
		std::vector<carl::Variable> eqVars(eqVarSet.begin(), eqVarSet.end());
		
		// Collect all coefficients and rhs
		std::vector<Rational> coef;
		for(const auto& it : mEquations){
			for (const auto& var : eqVars) {
				// if var in equation, choose coeff, otherwise 0
				bool found = false;
				for (const auto& term: it.lhs()) {
					if (term.isConstant()) continue;

					if (term.getSingleVariable() == var) {
						found = true;
						coef.push_back(term.coeff());
						break;
					}
				}

				if (!found) {
					coef.push_back(0);
				}
			}
			
			coef.push_back(-it.constantPart());
		}
		
		std::size_t rows = mEquations.size();
		std::size_t columns = eqVars.size();

		MatrixT matrix = MatrixT::Map(coef.data(), (long) columns + 1, (long) rows).transpose();

		SMTRAT_LOG_DEBUG("smtrat.gauss", matrix);

		//LU Decomposition
		Eigen::FullPivLU<MatrixT> lu(matrix);
		
		const MatrixT& u = lu.matrixLU().triangularView<Eigen::Upper>();
		const MatrixT& q = lu.permutationQ();
		const MatrixT& p = lu.permutationP();

		//newUpper with rhs and origin rows and columns order
		MatrixT newUpper = p.inverse() * u * q.inverse();
		VectorT newB = newUpper.col(newUpper.cols() - 1);
		newUpper.conservativeResize(newUpper.rows(), newUpper.cols() - 1);

		std::vector<carl::Relation> rels((std::size_t) newUpper.rows(), carl::Relation::EQ);
		if(mInequalities.size() == 0){
			return reconstructEqSystem(newUpper, newB, eqVarSet, rels);
		}else{
			return reduce(newUpper, newB, eqVarSet);
		}
	}

template<class Settings>
	FormulaT PBGaussModule<Settings>::reconstructEqSystem(const MatrixT& m, const VectorT& b, const carl::Variables& vars, const std::vector<carl::Relation>& rels){
		FormulasT subformulas;
		std::vector<carl::Variable> varsVec(vars.begin(), vars.end());
		for(long i = 0; i < m.rows(); i++){
			Poly newLHS;
			const VectorT& r = m.row(i);
			
			// Compute least common multiple of all denominators
			Rational mpl = 1;
			for (long rid = 0; rid < r.size(); rid++) {
				if (!carl::isInteger(r[rid])){
					mpl = carl::lcm(mpl, carl::getDenom(r[rid]));
				}
			}
			// Restore 
			for(long j = 0; j < r.size(); j++){
				if (carl::isZero(r[j])) continue;
				newLHS += TermT(Rational(mpl * r[j]) * varsVec[(std::size_t) j]);
			}
			subformulas.emplace_back(ConstraintT(newLHS + Rational(b[i] * -mpl), rels[std::size_t(i)]));
		}
		return FormulaT(carl::FormulaType::AND, std::move(subformulas));
	}


template<class Settings>
	FormulaT PBGaussModule<Settings>::reduce(const MatrixT& u, const VectorT& b, const carl::Variables vars){

		std::vector<Rational> normUVec;
		for(auto i = 0; i < u.rows(); i++){
			for(auto rid = 0; rid < u.row(i).size(); rid++){
				if(u.row(i)[i] != 0){
					normUVec.push_back(carl::div(u.row(i)[rid], u.row(i)[i]));
				}else{
					normUVec.push_back(u.row(i)[rid]);
				}
			}
		}


		MatrixT normU = MatrixT::Map(normUVec.data(), (long) u.cols(), (long) u.rows()).transpose();
		std::vector<Rational> bVector(b.data(), b.data() + b.size());

		//Resize normU and add b 
		std::vector<Rational> upperCoef;
		for(auto i = 0; i < normU.rows(); i++){
			VectorT r = normU.row(i);
			std::vector<Rational> row(r.data(), r.data() + r.size());
			for(auto j : mVariables){
				auto elem = vars.find(j);
				if(elem != vars.end()){
					upperCoef.push_back(row[(std::size_t) std::distance(vars.begin(), elem)]);
				}else{
					upperCoef.push_back((Rational) 0);
				}
			}
			upperCoef.push_back(bVector[(std::size_t) i]);
		}

		MatrixT uMatrix = MatrixT::Map(upperCoef.data(), (long) mVariables.size() + 1, (long) mEquations.size()).transpose();

		//Inequalities to matrix
		std::vector<carl::Relation> ineqRels;
		std::vector<Rational> ineqCoef;
		for(const auto& i : mInequalities){
			ineqRels.push_back(i.relation());
			auto iLHS = i.lhs();
			for(const auto& j : mVariables){
				auto elem = std::find_if(iLHS.begin(), iLHS.end(), 
					[&] (const TermT& elem){
						std::cout << elem << std::endl;
						return !elem.isConstant() && elem.getSingleVariable() == j;
					});
				if(elem != iLHS.end()){
					ineqCoef.push_back(elem->coeff());
				}else{
					ineqCoef.push_back(0);
				}
			}
			ineqCoef.push_back(i.constantPart());
		}


		MatrixT ineqMatrix = MatrixT::Map(ineqCoef.data(), (long) mVariables.size() + 1, (long) mInequalities.size()).transpose();

		MatrixT result(mVariables.size() + 1, 0);
		for(auto i = 0; i < ineqMatrix.rows();){
			const VectorT& row = ineqMatrix.row(i);

			//Check if possible to simplify
			Rational m;
			long column = -1;
			for(auto j = 0; j < row.size(); j++){
				if(row(j) != 0){
					column = j;
					break;
				}
			}
			Rational multiplier;
			if(column >= 0 && column < u.rows()){
				//Reduce

				//Look for row in u which can reduce the inequality
				VectorT eqRow;
				for(auto it = 0; it < uMatrix.rows(); it++){
					const VectorT& r = uMatrix.row(it);
					std::vector<Rational> testrowVec(r.data(), r.data() + r.size());
					for(auto colIterator = column; colIterator < row.size(); colIterator++){
						if(row(colIterator) == 0){
							it++;
							break;
						}else{
							bool found = false;
							if(colIterator == 0){
								if(r(0) == 1){
									eqRow = uMatrix.row(it);
									std::vector<Rational> eqRowVec(eqRow.data(), eqRow.data() + eqRow.size());
									//Check which sign the multiplier must have
									if((eqRow(colIterator) > 0 && row(colIterator) > 0) || (eqRow(colIterator) < 0 && row(colIterator) < 0)){
										multiplier = - row(colIterator);
									}else{
										multiplier = row(colIterator);
									}
									found = true;
									break;
								}
							}else{
								if(r(colIterator) == 1){
									//Check if entries before column-th column are 0
									bool zeros = true;
									for(auto k = 0; k < colIterator; k++){
										if(r(k) != 0){
											zeros = false;
											break;
										}
									}
									if(zeros){
										eqRow = uMatrix.row(it);
										std::vector<Rational> eqRowVec(eqRow.data(), eqRow.data() + eqRow.size());
										//Check which sign the multiplier must have
										if((eqRow(colIterator) > 0 && row(colIterator) > 0) || (eqRow(colIterator) < 0 && row(colIterator) < 0)){
											multiplier = - row(colIterator);
										}else{
											multiplier = row(colIterator);
										}
										found = true;
										break;
									}
								}
							}
							if(found) break;
						}
					}

				}


				std::vector<Rational> rowVec(row.data(), row.data() + row.size());
				std::vector<Rational> eqRowVec(eqRow.data(), eqRow.data() + eqRow.size());

				if(eqRowVec.size() != 0){
					ineqMatrix.row(i) = (multiplier * eqRow) + row; 
					//Update relation
					if(mInequalities[(std::size_t) i].relation() == carl::Relation::LESS){
						ineqRels[(std::size_t) i] = carl::Relation::LEQ;
					}else if(mInequalities[(std::size_t) i].relation() == carl::Relation::GREATER){
						ineqRels[(std::size_t) i] = carl::Relation::GEQ;
					}
					// Try again with this (simplified) row
					continue;
				}else{
					//Got to next row
					i++;
				}	
			}else {
				//It is not possible to simplify.
				result.conservativeResize(result.rows(), result.cols() + 1);
				result.col(result.cols()-1) = ineqMatrix.row(i);
				// Go to next row 
				i++;
			}
		}

		for (const auto& it : mEquations) {
			addSubformulaToPassedFormula(FormulaT(it));
		}

		MatrixT resultT = result.transpose();
		const VectorT& newB = resultT.col(resultT.cols() - 1);
		resultT.conservativeResize(resultT.rows(), resultT.cols() - 1);
		return  reconstructEqSystem(resultT, newB, mVariables, ineqRels);
	}
}

#include "Instantiation.h"
