/**
 * @file EMModule.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

#pragma once

#include "../PModule.h"
#include "EMStatistics.h"
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
			std::string moduleName() const {
				return SettingsType::moduleName;
			}
            EMModule( const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = NULL );

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
