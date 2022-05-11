/**
 * @file NewCADModule.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2016-02-23
 * Created on 2016-02-23.
 */

#pragma once

#include <smtrat-cad/CAD.h>
//#include <smtrat-cad/utils/CADPreprocessor.h>
#include <smtrat-cad/utils/Preprocessor.h>
#include <smtrat-variablebounds/VariableBounds.h>

#include <smtrat-solver/Module.h>
#include "NewCADStatistics.h"
#include "NewCADSettings.h"

namespace smtrat
{
	template<typename Settings>
	class NewCADModule : public Module
	{
		private:
#ifdef SMTRAT_DEVOPTION_Statistics
			NewCADStatistics& mStatistics = statistics_get<NewCADStatistics>(Settings::moduleName);
#endif
			/// Stores the polynomials seen during inform() to build the variable ordering.
			std::vector<Poly> mPolynomials;

			carl::carlVariables mVariables;
			cad::CAD<Settings> mCAD;
			cad::Assignment mLastAssignment;
			Model mLastModel;

			cad::Preprocessor mPreprocessor;
			
			void addConstraint(const ConstraintT& c) {
				mPreprocessor.addConstraint(c);
			}
			void removeConstraint(const ConstraintT& c) {
				mPreprocessor.removeConstraint(c);
			}
			void pushConstraintsToReplacer() {
				for (const auto& f: rReceivedFormula()) {
					assert(f.formula().type() == carl::FormulaType::CONSTRAINT);
					addConstraint(f.formula().constraint());
				}
			}
			void removeConstraintsFromReplacer() {
				//while (!mPreprocessor.inequalities().empty()) {
				//	mPreprocessor.removeConstraint(mPreprocessor.inequalities().begin()->first);
				//}
				//while (!mPreprocessor.equalities().empty()) {
				//	mPreprocessor.removeConstraint(mPreprocessor.equalities().front());
				//}
				//mPreprocessor.preprocess();
				mPreprocessor.clear();
			}

		public:
			typedef Settings SettingsType;
			std::string moduleName() const {
				return SettingsType::moduleName;
			}
			NewCADModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = nullptr);

			~NewCADModule();
			
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
			 * @param _full false, if this module should avoid too expensive procedures and rather return unknown instead.
                         * @param _objective if not set to NO_VARIABLE, the module should find an assignment minimizing this objective variable; otherwise any assignment is good.
			 * @return True,	if the received formula is satisfiable;
			 *		 False,   if the received formula is not satisfiable;
			 *		 Unknown, otherwise.
			 */
			Answer checkCore();
	};
}
