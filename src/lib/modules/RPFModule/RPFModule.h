/**
 * Removes redundant or obsolete factors of polynomials from the formula.
 * 
 * @file RPFModule.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

#pragma once

#include "../../solver/Module.h"
#include "RPFStatistics.h"
#include "RPFSettings.h"
#include "../../datastructures/VariableBounds.h"

namespace smtrat
{
    template<typename Settings>
    class RPFModule : public Module
    {
        private:
            // Members.
            ///
			carl::FormulaVisitor<FormulaT> visitor;
			/// Collection of bounds of all received formulas.
			vb::VariableBounds<FormulaT> varbounds;

        public:
            RPFModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = NULL );

            ~RPFModule();

            // Main interfaces.

            /**
             * Informs the module about the given constraint. It should be tried to inform this
             * module about any constraint it could receive eventually before assertSubformula
             * is called (preferably for the first time, but at least before adding a formula
             * containing that constraint).
             * @param _constraint The constraint to inform about.
             * @return false, if it can be easily decided whether the given constraint is inconsistent;
             *          true, otherwise.
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
            
			EvalRationalIntervalMap completeBounds(const Poly& p) const {
				auto res = varbounds.getEvalIntervalMap();
				for (auto var: p.gatherVariables()) {
					if (res.find(var) == res.end()) {
						res[var] = RationalInterval::unboundedInterval();
					}
				}
				return res;
			}
            
			/**
			 * Removes redundant or obsolete factors of polynomials from the formula.
             */
			FormulaT removeFactors(const FormulaT& formula);
			std::function<FormulaT(FormulaT)> removeFactorsFunction;

    };
}

#include "RPFModule.tpp"

#include "RPFModuleInstantiation.h"
