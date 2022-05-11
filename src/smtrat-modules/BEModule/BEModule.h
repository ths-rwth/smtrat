/**
 * A module, which searches for bounds of arithmetic variables and polynomials.
 * 
 * @file BEModule.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-09-09
 * Created on 2015-09-09.
 */

#pragma once

#include <smtrat-solver/PModule.h>
#include "BESettings.h"
#include <carl-formula/formula/functions/ConstraintBounds.h>

namespace smtrat
{
    template<typename Settings>
    class BEModule : public PModule
    {
        private:
            // Members.
            ///
			
			using Choice = std::tuple<carl::Variable,FormulaT>;
			std::map<Choice, carl::Variable> mReplacements;

        public:
			typedef Settings SettingsType;
			std::string moduleName() const {
				return SettingsType::moduleName;
			}
            BEModule( const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = NULL );

            ~BEModule();

            // Main interfaces.

            /**
             * Checks the received formula for consistency.
             * @return SAT,    if the received formula is satisfiable;
             *         UNSAT,   if the received formula is not satisfiable;
             *         Unknown, otherwise.
             */
            Answer checkCore();

        private:
            FormulaT extractBounds( const FormulaT& formula );
			std::function<FormulaT(FormulaT)> extractBoundsFunction;
			
			void collectBounds(carl::ConstraintBounds<Poly>& cb, const FormulaT& formula, bool conjunction) const;
			FormulaT applyReplacements(const FormulaT& f) const;
    };
}
