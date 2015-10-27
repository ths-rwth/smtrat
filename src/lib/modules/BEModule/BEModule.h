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

#include "../../solver/PModule.h"
#include "BEStatistics.h"
#include "BESettings.h"

namespace smtrat
{
    template<typename Settings>
    class BEModule : public PModule
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
            BEModule( const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = NULL );

            ~BEModule();

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
            FormulaT extractBounds( const FormulaT& formula );
			std::function<FormulaT(FormulaT)> extractBoundsFunction;
    };
}

#include "BEModule.tpp"

#include "BEModuleInstantiation.h"
