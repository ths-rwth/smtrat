/**
 * @file EMModule.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

#pragma once

#include <smtrat-solver/PModule.h>
#include "EMSettings.h"

namespace smtrat
{
    template<typename Settings>
    class EMModule : public PModule
    {
        private:
            // Members.
            ///
			carl::FormulaVisitor<FormulaT> mVisitor;

        public:
			typedef Settings SettingsType;
            EMModule( const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = NULL );

            ~EMModule();

            // Main interfaces.

            /**
             * Checks the received formula for consistency.
             * @return SAT,    if the received formula is satisfiable;
             *         UNSAT,   if the received formula is not satisfiable;
             *         Unknown, otherwise.
             */
            Answer checkCore();
        
        private:
                
			FormulaT eliminateEquation(const FormulaT& formula);
			std::function<FormulaT(FormulaT)> eliminateEquationFunction;

    };
}
