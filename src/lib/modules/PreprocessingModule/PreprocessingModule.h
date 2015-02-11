/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */


/**
 * @file   PreprocessingModule.h
 *         Created on January 10, 2013, 9:59 PM
 * @author: Sebastian Junges
 *
 *
 */

#pragma once

#include "../../solver/Module.h"
#include "../../datastructures/VariableBounds.h"
#include "PreprocessingSettings.h"

namespace smtrat
{
    /**
     *
     */
	template<typename Settings>
    class PreprocessingModule : public Module
    {
		private:
			static constexpr bool collectBounds = Settings::checkBounds;
        protected:
			vb::VariableBounds<FormulaT> varbounds;
			carl::FormulaVisitor<FormulaT> visitor;
			
			FormulasT tmpOrigins;
			void accumulateBoundOrigins(const ConstraintT& constraint) {
				auto tmp = varbounds.getOriginsOfBounds(constraint.variables());
				tmpOrigins.insert(tmp.begin(), tmp.end());
			}

        public:

            PreprocessingModule( ModuleType _type, const ModuleInput*, RuntimeSettings*, Conditionals&, Manager* const = nullptr );

            /**
             * Destructor:
             */
            virtual ~PreprocessingModule();

            /**
             * Methods:
             */

            // Interfaces.
            bool assertSubformula( ModuleInput::const_iterator );
            Answer isConsistent();
            void removeSubformula( ModuleInput::const_iterator );
			void updateModel() const;

        protected:
			/// Bounds that have been added since the last call to isConsistent().
			std::set<FormulaT> newBounds;
			bool addBounds(FormulaT formula);
			void removeBounds(FormulaT formula);
			
			/**
			 * Removes redundant or obsolete factors of polynomials from the formula.
             */
			FormulaT removeFactors(FormulaT formula);
			std::function<FormulaT(FormulaT)> removeFactorsFunction;
			
			/**
			 * Checks if constraints vanish using the variable bounds.
			 */
			FormulaT checkBounds(FormulaT formula);
			std::function<FormulaT(FormulaT)> checkBoundsFunction;
    };

}    // namespace smtrat

#include "PreprocessingModule.tpp"