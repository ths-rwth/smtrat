/**
 * Splits the sum-of-squares (sos) decomposition of all constraints with a sos as left-hand side.
 * 
 * @file SplitSOSModule.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

#pragma once

#include "../PModule.h"
#include "SplitSOSStatistics.h"
#include "SplitSOSSettings.h"

namespace smtrat
{
    template<typename Settings>
    class SplitSOSModule : public PModule
    {
        private:
            // Members.
            ///
			carl::FormulaVisitor<FormulaT> mVisitor;

        public:
			typedef Settings SettingsType;
std::string moduleName() const {
return SettingsType::moduleName;
}
            SplitSOSModule( const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = NULL );

            ~SplitSOSModule();

            // Main interfaces.

            /**
             * Checks the received formula for consistency.
             * @return SAT,    if the received formula is satisfiable;
             *         UNSAT,   if the received formula is not satisfiable;
             *         Unknown, otherwise.
             */
            Answer checkCore();

        private:
            
			/**
			 * Splits the sum-of-squares (sos) decomposition, if the given formula is a constraint with a sos as left-hand side.
             */
			FormulaT splitSOS(const FormulaT& formula);
			std::function<FormulaT(FormulaT)> splitSOSFunction;
    };
}
