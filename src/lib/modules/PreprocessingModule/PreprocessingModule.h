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
			// If anything that needs variable bounds is active, we shall collect the bounds.
			static constexpr bool collectBounds = Settings::checkBounds;
        protected:
			vb::VariableBounds<FormulaT> varbounds;
			carl::FormulaVisitor<FormulaT> visitor;
			
			FormulasT tmpOrigins;
			void accumulateBoundOrigins(const ConstraintT& constraint) {
				auto tmp = varbounds.getOriginsOfBounds(constraint.variables());
				tmpOrigins.insert(tmp.begin(), tmp.end());
			}
			EvalRationalIntervalMap completeBounds(const Poly& p) const {
				auto res = varbounds.getEvalIntervalMap();
				for (auto var: p.gatherVariables()) {
					if (res.find(var) == res.end()) {
						res[var] = RationalInterval::unboundedInterval();
					}
				}
				return res;
			}
			EvalRationalIntervalMap completeBounds(const ConstraintT& c) const {
				auto res = varbounds.getEvalIntervalMap();
				for (auto var: c.variables()) {
					if (res.find(var) == res.end()) {
						res[var] = RationalInterval::unboundedInterval();
					}
				}
				return res;
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
            bool addCore( ModuleInput::const_iterator );
            Answer checkCore( bool _full );
            void removeCore( ModuleInput::const_iterator );
			void updateModel() const;

        protected:
			/// Bounds that have been added since the last call to isConsistent().
			std::set<FormulaT> newBounds;
			bool addBounds(const FormulaT& formula);
			void removeBounds(const FormulaT& formula);
			
			/**
			 * Removes redundant or obsolete factors of polynomials from the formula.
             */
			FormulaT removeFactors(const FormulaT& formula);
			std::function<FormulaT(FormulaT)> removeFactorsFunction;
			
			/**
			 * Splits the sum-of-squares (sos) decomposition, if the given formula is a constraint with a sos as left-hand side.
             */
			FormulaT splitSOS(const FormulaT& formula);
			std::function<FormulaT(FormulaT)> splitSOSFunction;
			
			/**
			 * Checks if constraints vanish using the variable bounds.
			 */
			FormulaT checkBounds(const FormulaT& formula);
			std::function<FormulaT(FormulaT)> checkBoundsFunction;
    };

}    // namespace smtrat

#include "PreprocessingModule.tpp"