/**
 * @file CubeLIAModule.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-11-24
 * Created on 2015-11-24.
 */

#pragma once

#include "../../solver/Module.h"
#include "CubeLIAStatistics.h"
#include "CubeLIASettings.h"
#include "../LRAModule/LRAModule.h"

namespace smtrat
{
	template<typename Settings>
	class CubeLIAModule : public Module
	{
		private:
            
            struct Cubification
            {
                FormulaT mCubification;
                ModuleInput::iterator mPosition;
                std::size_t mUsages;
                
                Cubification() = delete;
                
                Cubification( const FormulaT& _cubification, ModuleInput::iterator _position ):
                    mCubification(_cubification),
                    mPosition(_position),
                    mUsages(1)
                {}
            };
			// Members.
            mutable bool mModelUpdated;
            std::map<carl::Variable,Poly> mIntToRealVarMap;
            std::map<carl::Variable,carl::Variable> mRealToIntVarMap;
            carl::FastMap<FormulaT,Cubification> mCubifications;
            ModuleInput* mLRAFormula;
            std::vector<std::atomic_bool*> mLRAFoundAnswer;
            RuntimeSettings* mLRARuntimeSettings;
            LRAModule<LRASettings1> mLRA;
            
#ifdef SMTRAT_DEVOPTION_Statistics
			CubeLIAStatistics mStatistics;
#endif
			
		public:
			typedef Settings SettingsType;
			std::string moduleName() const {
				return SettingsType::moduleName;
			}
			CubeLIAModule(const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = nullptr);

			~CubeLIAModule();
			
			// Main interfaces.

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
			 * @return SAT,	if the received formula is satisfiable;
			 *		 UNSAT,   if the received formula is not satisfiable;
			 *		 Unknown, otherwise.
			 */
			Answer checkCore();
            
	};
}
