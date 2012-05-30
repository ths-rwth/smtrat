/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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
 * @file TSManager.h
 *
 * @author Florian Corzilius
 * @author Ulrich Loup
 * @author Sebastian Junges
 * @since 2012-01-18
 * @version 2012-02-11
 */

#ifndef SMTRAT_TSMANAGER_H
#define SMTRAT_TSMANAGER_H

#include <vector>

#include "Constraint.h"
#include "Answer.h"
#include "ModuleFactory.h"
#include "Strategy.h"
#include "ModuleType.h"
#include "Module.h"
#include "modules/StandardModuleFactory.h"

namespace smtrat
{
    /**
     * Base class for solvers. This is the interface to the user.
     */
    class Manager
    {
        private:

            /// the symbol table containing the variables of all constraints
            GiNaC::symtab mAllVariables;
            /// for each string representation its constraint (considering all constraints of which the manager has already been informed)
            std::map<const std::string, Constraint*> mAllConstraints;
            /// the constraints so far passed to the primary backend
            Formula* mpPassedFormula;
            /// all generated instances of modules
            std::vector<Module*> mGeneratedModules;
            /// a mapping of each module to its backends
            std::map<const Module* const , std::vector<Module*> > mBackendsOfModules;
            /// the primary backends
            Module* mpPrimaryBackend;
            /// the backtrack points
            std::vector<unsigned> mBackTrackPoints;
            /// a Boolean showing whether the manager has received new constraint after the last consistency check
            bool mBackendsUptodate;
            /// modules we can use
            std::map<const ModuleType, ModuleFactory*>* mpModulFactories;
            /// primary strategy
            Strategy* mpStrategy;

        public:
            Manager( Formula* = new Formula( AND ) );
            virtual ~Manager();

            inline Answer isConsistent()
            {
                return mpPrimaryBackend->isConsistent();
            }

            inline void pushBacktrackPoint()
            {
                mBackTrackPoints.push_back( mpPassedFormula->size() );
                mpPrimaryBackend->pushBacktrackPoint();
            }

            inline const GiNaC::symtab allVariables() const
            {
                return mAllVariables;
            }

            inline const std::map<const ModuleType, ModuleFactory*>& rModulFactories() const
            {
                return *mpModulFactories;
            }

            inline void addModuleType( const ModuleType _moduleType, ModuleFactory* _factory )
            {
                mpModulFactories->insert( std::pair<const ModuleType, ModuleFactory*>( _moduleType, _factory ) );
            }

            inline Strategy& strategy()
            {
                return *mpStrategy;
            }

            inline std::vector<Module*> getAllBackends( Module* _module )
            {
                return mBackendsOfModules[_module];
            }

            inline unsigned uniqueModuleNumber( const Module* const _module )
            {
                unsigned                             result     = 0;
                std::vector<Module*>::const_iterator moduleIter = mGeneratedModules.begin();
                while( moduleIter != mGeneratedModules.end() )
                {
                    if( *moduleIter == _module )
                    {
                        return result;
                    }
                    ++moduleIter;
                    ++result;
                }
                assert( false );
            }

            bool inform( const std::string&, bool );
            void popBacktrackPoint();
            bool addConstraint( const std::string&, const bool, const bool );
            std::vector<std::vector<unsigned> > getReasons() const;
            std::vector<Module*> getBackends( Formula*, Module* );
            std::vector<ModuleFactory*> getBackendsFactories( Formula* const , Module* ) const;

        private:

            /*
             * Auxiliary Methods
             */
            Constraint stringToConstraint( const std::string&, const bool, const bool );
            static std::string prefixToInfix( const std::string& );
            static const GiNaC::ex toRationalExpression( const GiNaC::ex& p, const vector<GiNaC::symbol>& symbolLst );

            static const GiNaC::ex toRationalExpression( const GiNaC::ex& p, GiNaC::symtab v )
            {
                std::vector<GiNaC::symbol> symbolLst;
                for( register GiNaC::symtab::const_iterator i = v.begin(); i != v.end(); ++i )
                    symbolLst.push_back( GiNaC::ex_to<GiNaC::symbol>( i->second ) );
                return toRationalExpression( p, symbolLst );
            }

            static void isolateByVariables( const GiNaC::ex& polynomial,
                                            const vector<GiNaC::symbol>& symbolLst,
                                            GiNaC::ex& coefficient,
                                            GiNaC::ex& monomial );
            static bool is_constant( const GiNaC::ex& polynomial, const vector<GiNaC::symbol>& symbolLst );
    };

}    // namespace smtrat

#endif   /** SMTRAT_TSMANAGER_H */
