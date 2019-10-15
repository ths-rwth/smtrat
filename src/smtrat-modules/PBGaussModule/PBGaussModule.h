/**
 * 
 * Supports optimization.
 * 
 * @file PBGaussModule.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2017-05-03
 * Created on 2017-05-03.
 */

#pragma once

#include <eigen3/Eigen/Core>
#include <eigen3/Eigen/LU>

#include <smtrat-solver/Module.h>
#include "PBGaussSettings.h"

namespace smtrat
{
	template<typename Settings>
	class PBGaussModule : public Module
	{
	public:
		using MatrixT = Eigen::Matrix<Rational, Eigen::Dynamic, Eigen::Dynamic>;
		using VectorT = Eigen::Matrix<Rational, Eigen::Dynamic, 1>;
		
		private:
			// Members.
			carl::Variables mVariables;
			std::vector<ConstraintT> mEquations;
			std::vector<ConstraintT> mInequalities;

			
		public:
			typedef Settings SettingsType;
			std::string moduleName() const {
				return SettingsType::moduleName;
			}
			PBGaussModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = nullptr);

			~PBGaussModule();
			
			// Main interfaces.
			/**
			 * Informs the module about the given constraint. It should be tried to inform this
			 * module about any constraint it could receive eventually before assertSubformula
			 * is called (preferably for the first time, but at least before adding a formula
			 * containing that constraint).
			 * @param _constraint The constraint to inform about.
			 * @return false, if it can be easily decided whether the given constraint is inconsistent;
			 *		  true, otherwise.
			 */
			bool informCore( const FormulaT& _constraint );

			/**
			 * Informs all backends about the so far encountered constraints, which have not yet been communicated.
			 * This method must not and will not be called more than once and only before the first runBackends call.
			 */
			void init();

			/**
			 * The module has to take the given sub-formula of the received formula into account.
			 *
			 * @param _subformula The sub-formula to take additionally into account.
			 * @return false, if it can be easily decided that this sub-formula causes a conflict with
			 *		  the already considered sub-formulas;
			 *		  true, otherwise.
			 */
			bool addCore( ModuleInput::const_iterator _subformula );

			/**
			 * Removes the subformula of the received formula at the given position to the considered ones of this module.
			 * Note that this includes every stored calculation which depended on this subformula, but should keep the other
			 * stored calculation, if possible, untouched.
			 *
			 * @param _subformula The position of the subformula to remove.
			 */
			void removeCore( ModuleInput::const_iterator _subformula );

			/**
			 * Updates the current assignment into the model.
			 * Note, that this is a unique but possibly symbolic assignment maybe containing newly introduced variables.
			 */
			void updateModel() const;

			/**
			 * Checks the received formula for consistency.
			 * @return True,	if the received formula is satisfiable;
			 *		 False,   if the received formula is not satisfiable;
			 *		 Unknown, otherwise.
			 */
			Answer checkCore();
			
			/// Convenience wrapper for Eigen::conservativeResizeLike with a zero vector.
			static void conservativeResize(VectorT& v, long newSize) {
				v.conservativeResizeLike(VectorT::Zero(newSize));
			}
			/// Convenience wrapper for Eigen::conservativeResizeLike with a zero matrix.
			static void conservativeResize(MatrixT& m, long newRows, long newCols) {
				m.conservativeResizeLike(MatrixT::Zero(newRows, newCols));
			}

			FormulaT gaussAlgorithm();
			FormulaT reconstructEqSystem(const MatrixT& m, const VectorT& b, const carl::Variables& vars, const std::vector<carl::Relation>& rels);
			FormulaT reduce(const MatrixT& u, const VectorT& b, const carl::Variables vars);
			std::vector<Rational> lookForReductionRow(const MatrixT& uMatrix, const VectorT& ineqRow, long column);

	};
}
