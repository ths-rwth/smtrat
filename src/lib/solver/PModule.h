/**
 * All preprocessing modules shall derive from this module, that is modules, which simplify 
 * their received formula to an equisatisfiable formula being passed to their backends.
 * 
 * @file PModule.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-09-09
 * Created on 2015-09-09.
 */

#pragma once

#include "Module.h"

namespace smtrat
{
    class PModule : public Module
    {
        private:
            bool mAppliedPreprocessing;
        public:
            
            PModule( const ModuleInput* _formula, Conditionals& _foundAnswer, Manager* _manager = NULL );

            /**
             * @return true, if this module is a preprocessor that is a module, which simplifies
             *         its received formula to an equisatisfiable formula being passed to its backends.
             *         The simplified formula can be obtained with getReceivedFormulaSimplified().
             */
            bool isPreprocessor() const
            {
                return false;
            }
            
            /**
             * @return true, if the current received formula has been simplified and the result of this simplification
             *         is stored in the passed formula.
             */
            bool appliedPreprocessing() const
            {
                return mAppliedPreprocessing;
            }
            
            /**
             * The module has to take the given sub-formula of the received formula into account.
             *
             * @param _subformula The sub-formula to take additionally into account.
             * @return false, if it can be easily decided that this sub-formula causes a conflict with
             *          the already considered sub-formulas;
             *          true, otherwise.
             */
            bool add( ModuleInput::const_iterator _subformula );
            
            /**
             * Removes everything related to the given sub-formula of the received formula. However,
             * it is desired not to lose track of search spaces where no satisfying  assignment can 
             * be found for the remaining sub-formulas.
             *
             * @param _subformula The sub formula of the received formula to remove.
             */
            void remove( ModuleInput::const_iterator _subformula );
            
            /**
             * Runs the backend solvers on the passed formula.
             * @param _full false, if this module should avoid too expensive procedures and rather return unknown instead.
             * @param _minimize true, if the module should find an assignment minimizing its objective variable; otherwise any assignment is good.
             * @return True,    if the passed formula is consistent;
             *          False,   if the passed formula is inconsistent;
             *          Unknown, otherwise.
             */
            Answer runBackends( bool _full = true, bool _minimize = false );
            
            /**
             * @return A pair of a Boolean and a formula, where the Boolean is true, if the received formula 
             *         could be simplified to an equisatisfiable formula. The formula is equisatisfiable to this
             *         module's reveived formula, if the Boolean is true.
             */
            std::pair<bool,FormulaT> getReceivedFormulaSimplified();
    };
}
