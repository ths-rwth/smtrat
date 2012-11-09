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
 * @file TSManager.cpp
 * @author Florian Corzilius
 * @author Ulrich Loup
 * @author Sebastian Junges
 *
 * @since 2012-01-18, 3:22 PM
 */

#include "Manager.h"
#include "modules/Modules.h"
#include "StrategyGraph.h"

#include <typeinfo>
#include <cln/cln.h>

using namespace std;

using GiNaC::ex;
using GiNaC::numeric;
using GiNaC::symbol;

namespace smtrat
{
    /**
     * Constructors:
     */

    Manager::Manager( Formula* _inputFormula ):
        mpPassedFormula( _inputFormula ),
        mGeneratedModules( vector<Module*>( 1, new Module( mpPassedFormula, this ) ) ),
        mBackendsOfModules(),
        mpPrimaryBackend( mGeneratedModules.back() ),
        mStrategyGraph(),
        mModulePositionInStrategy()
    {
        mpModulFactories = new map<const ModuleType, ModuleFactory*>();
        mModulePositionInStrategy[mpPrimaryBackend] = 0;

        // inform it about all constraints
        for( fcs_const_iterator constraint = Formula::mConstraintPool.begin(); constraint != Formula::mConstraintPool.end(); ++constraint )
        {
            mpPrimaryBackend->inform( *constraint );
        }

        /*
         * Add all existing modules.
         */
        addModuleType( MT_SmartSimplifier, new StandardModuleFactory<SmartSimplifier>() );
#ifdef USE_GB
        addModuleType( MT_GroebnerModule, new StandardModuleFactory<GroebnerModule<GBSettings> >() );
        #endif
        addModuleType( MT_VSModule, new StandardModuleFactory<VSModule>() );
        #ifdef USE_CAD
        //        addModuleType( MT_UnivariateCADModule, new StandardModuleFactory<UnivariateCADModule>() );
        addModuleType( MT_CADModule, new StandardModuleFactory<CADModule>() );
        #endif
        addModuleType( MT_SATModule, new StandardModuleFactory<SATModule>() );
        addModuleType( MT_PreProModule, new StandardModuleFactory<PreProModule>() );
        addModuleType( MT_CNFerModule, new StandardModuleFactory<CNFerModule>() );
        addModuleType( MT_LRAModule, new StandardModuleFactory<LRAModule>() );
        addModuleType( MT_SingleVSModule, new StandardModuleFactory<SingleVSModule>() );
//        addModuleType( MT_ICPModule, new StandardModuleFactory<ICPModule>() );
    }

    /**
     * Destructor:
     */

    Manager::~Manager()
    {
        Module::storeAssumptionsToCheck( *this );
        while( !mGeneratedModules.empty() )
        {
            Module* ptsmodule = mGeneratedModules.back();
            mGeneratedModules.pop_back();
            delete ptsmodule;
        }
        while( !mpModulFactories->empty() )
        {
            const ModuleFactory* pModulFactory = mpModulFactories->begin()->second;
            mpModulFactories->erase( mpModulFactories->begin() );
            delete pModulFactory;
        }
        delete mpModulFactories;
    }

    /**
     * Methods:
     */

    /**
     * Prints the model, if there is one.
     *
     * @param _out The stream to print on.
     */
    void Manager::printModel( ostream& _out ) const
    {
        mpPrimaryBackend->updateModel();
        if( !mpPrimaryBackend->model().empty() )
        {
            _out << "Model:" << endl;
            for( Module::Model::const_iterator assignment = mpPrimaryBackend->model().begin(); assignment != mpPrimaryBackend->model().end(); ++assignment )
            {
                _out << "  ";
                _out << left << setw( Formula::constraintPool().maxLenghtOfVarName() ) << assignment->first;
                _out << " -> " << assignment->second << endl;
            }
        }
    }

    /**
     * Get the backends to call for the given problem instance required by the given module.
     *
     * @param _formula      The problem instance.
     * @param _requiredBy   The module asking for a backend.
     *
     * @return  A vector of modules, which the module defined by _requiredBy calls in parallel to achieve
     *          an answer to the given instance.
     */
    vector<Module*> Manager::getBackends( Formula* _formula, Module* _requiredBy )
    {
        vector<Module*>        backends         = vector<Module*>();
        vector<Module*>&       allBackends      = mBackendsOfModules[_requiredBy];
        vector< pair<unsigned, ModuleType> > backendModuleTypes = mStrategyGraph.nextModuleTypes( mModulePositionInStrategy[_requiredBy], _formula->getPropositions() );
        for( auto iter = backendModuleTypes.begin(); iter != backendModuleTypes.end(); ++iter )
        {
            assert( iter->second != _requiredBy->type() );
            vector<Module*>::iterator backend = allBackends.begin();
            while( backend != allBackends.end() )
            {
                if( (*backend)->type() == iter->second )
                {
                    // the backend already exists
                    backends.push_back( *backend );
                    break;
                }
                ++backend;
            }
            if( backend == allBackends.end() )
            {
                auto backendFactory = mpModulFactories->find( iter->second );
                assert( backendFactory != mpModulFactories->end() );
                // backend does not exist => create it
                Module* pBackend = backendFactory->second->create( _requiredBy->pPassedFormula(), this );
                mGeneratedModules.push_back( pBackend );
                pBackend->setId( mGeneratedModules.size()-1 );
                allBackends.push_back( pBackend );
                backends.push_back( pBackend );
                mModulePositionInStrategy[pBackend] = iter->first;
                // inform it about all constraints
                for( fcs_const_iterator constraint = _requiredBy->constraintsToInform().begin();
                        constraint != _requiredBy->constraintsToInform().end(); ++constraint )
                {
                    pBackend->inform( *constraint );
                }
            }
        }
        return backends;
    }

}    // namespace smtrat

