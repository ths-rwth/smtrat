/**
 * Checks if constraints vanish using bounds of the variable being extracted from the received constraints.
 * 
 * @file CBModule.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

#pragma once

#include "../../solver/PModule.h"
#include "CBStatistics.h"
#include "CBSettings.h"
#include "../../datastructures/VariableBounds.h"

namespace smtrat
{
    template<typename Settings>
    class CBModule : public PModule
    {
        private:
            // Members.
            ///
			carl::FormulaVisitor<FormulaT> visitor;
			/// Bounds that have been added since the last call to isConsistent().
			std::unordered_set<FormulaT> newBounds;
			/// Collection of bounds of all received formulas.
			vb::VariableBounds<FormulaT> varbounds;
            ///
			FormulaSetT tmpOrigins;

        public:
            CBModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = NULL );

            ~CBModule();

            // Main interfaces.

            /**
             * The module has to take the given sub-formula of the received formula into account.
             *
             * @param _subformula The sub-formula to take additionally into account.
             * @return false, if it can be easily decided that this sub-formula causes a conflict with
             *          the already considered sub-formulas;
             *          true, otherwise.
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
             * Checks the received formula for consistency.
             * @param _full false, if this module should avoid too expensive procedures and rather return unknown instead.
             * @return True,    if the received formula is satisfiable;
             *         False,   if the received formula is not satisfiable;
             *         Unknown, otherwise.
             */
            Answer checkCore( bool _full );

        private:
            
			void accumulateBoundOrigins(const ConstraintT& constraint) {
				auto tmp = varbounds.getOriginsOfBounds(constraint.variables());
				tmpOrigins.insert(tmp.begin(), tmp.end());
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
            
			void addBounds(const FormulaT& formula, const FormulaT& _origin);
            
			void removeBounds(const FormulaT& formula, const FormulaT& _origin);
			
			/**
			 * Checks if constraints vanish using the variable bounds.
			 */
			FormulaT checkBounds(const FormulaT& formula);
			std::function<FormulaT(FormulaT)> checkBoundsFunction;
    };
}

#include "CBModule.tpp"

#include "CBModuleInstantiation.h"
