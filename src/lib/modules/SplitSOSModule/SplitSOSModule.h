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

#include "../../solver/PModule.h"
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
            SplitSOSModule( const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = NULL );

            ~SplitSOSModule();

            // Main interfaces.

            /**
             * Checks the received formula for consistency.
             * @param _full false, if this module should avoid too expensive procedures and rather return unknown instead.
             * @return True,    if the received formula is satisfiable;
             *         False,   if the received formula is not satisfiable;
             *         Unknown, otherwise.
             */
            Answer checkCore( bool _full );

        private:
            
			/**
			 * Splits the sum-of-squares (sos) decomposition, if the given formula is a constraint with a sos as left-hand side.
             */
			FormulaT splitSOS(const FormulaT& formula);
			std::function<FormulaT(FormulaT)> splitSOSFunction;
    };
}

#include "SplitSOSModule.tpp"

#include "SplitSOSModuleInstantiation.h"
