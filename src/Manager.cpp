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
 * Created on January 18, 2012, 3:22 PM
 */
#include "Manager.h"
#include "modules/Modules.h"

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
        mGeneratedModules( vector<Module*>( 1, new Module( this, mpPassedFormula ))),
        mBackendsOfModules( map<const Module* const , vector<Module*> >() ),
        mpPrimaryBackend( mGeneratedModules.back() ),
        mBackTrackPoints( vector<unsigned>() )
    {
        mpStrategy       = new Strategy();
        mpModulFactories = new map<const ModuleType, ModuleFactory*>();

        // inform it about all constraints
        for( fcs_const_iterator constraint = Formula::mConstraintPool.begin();
                constraint != Formula::mConstraintPool.end();
                ++constraint )
        {
            mpPrimaryBackend->inform( *constraint );
        }

        /*
         * Add all existing modules.
         */
        addModuleType( MT_SmartSimplifier, new StandardModuleFactory<SmartSimplifier>() );
#ifdef USE_GB
        addModuleType( MT_GroebnerModule, new StandardModuleFactory<GroebnerModule>() );
#endif
        addModuleType( MT_VSModule, new StandardModuleFactory<VSModule>() );
#ifdef USE_CAD
        addModuleType( MT_UnivariateCADModule, new StandardModuleFactory<UnivariateCADModule>() );
        addModuleType( MT_CADModule, new StandardModuleFactory<CADModule>() );
#endif
        addModuleType( MT_SATModule, new StandardModuleFactory<SATModule>() );
        addModuleType( MT_PreProModule, new StandardModuleFactory<PreProModule>() );
        addModuleType( MT_CNFerModule, new StandardModuleFactory<CNFerModule>() );
        addModuleType( MT_LRAOneModule, new StandardModuleFactory<LRAOneModule>() );
        addModuleType( MT_LRATwoModule, new StandardModuleFactory<LRATwoModule>() );
        addModuleType( MT_SingleVSModule, new StandardModuleFactory<SingleVSModule>() );
        addModuleType( MT_FourierMotzkinSimplifier, new StandardModuleFactory<FourierMotzkinSimplifier>() );
    }

    /**
     * Destructor:
     */

    Manager::~Manager()
    {
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
        delete mpStrategy;
    }

    /**
     * Methods:
     */

    /**
     * Informs the manager and all modules which will be created about the existence of the given
     * constraint. The constraint is in form of a string either in infix or in prefix notation.
     * If the polarity of the literal, to which the given constraint belongs to, is negative
     * (false), the constraints is added inverted.
     *
     * @param _constraint   The constraint to add as string in either infix or prefix notation.
     * @param _infix        A flag which is true, if the constraint is given in infix notation,
     *                      and false, if it is given in prefix notation.
     *
     * @return  false,      if it is easy to decide whether the constraint is inconsistent;
     *          true,       otherwise.
     */
    bool Manager::inform( const string& _constraint, const bool _infix )
    {
        return Formula::newConstraint( _constraint, _infix, true )->isConsistent();
    }

	/**
     * Pops a backtrack point from the stack of backtrackpoints. Furthermore, it provokes popBacktrackPoint
     * in all so far created modules.
     */
	void Manager::popBacktrackPoint()
	{
        assert( !mBackTrackPoints.empty() );
        unsigned pos = 0;
        Formula::iterator subformula = mpPassedFormula->begin();
        while( pos <= mBackTrackPoints.back() )
        {
            ++subformula;
        }
        while( subformula != mpPassedFormula->end() )
        {
            mpPrimaryBackend->removeSubformula( subformula );
            subformula = mpPassedFormula->erase( subformula );
        }
        mBackTrackPoints.pop_back();
	}

    /**
     * Adds a constraint to the module of this manager. The constraint is in form of a string
     * either in infix or in prefix notation. If the polarity of the literal, to which the given
     * constraint belongs to, is negative (false), the constraints is added inverted.
     *
     * @param _constraint   The constraint to add as string in either infix or prefix notation.
     * @param _infix        A flag which is true, if the constraint is given in infix notation,
     *                      and false, if it is given in prefix notation.
     * @param _polarity     The polarity if the literal the constraint belongs to.
     *
     * @return  false,      if it is easy to decide whether the constraint is inconsistent;
     *          true,       otherwise.
     */
    bool Manager::addConstraint( const string& _constraint, const bool _infix, const bool _polarity )
    {
        /*
         * Add the constraint to the primary backend module.
         */
        mBackendsUptodate = false;

        mpPassedFormula->addSubformula( Formula::newConstraint( _constraint, _infix, _polarity ) );
        return mpPrimaryBackend->assertSubformula( mpPassedFormula->last() );
    }

    /**
     * Gets the infeasible subsets.
     *
     * @return  One or more infeasible subsets. An infeasible subset is a set of
     *          numbers, where the number i belongs to the ith received constraint.
     */
    vector<vector<unsigned> > Manager::getReasons() const
    {
        vector<vector<unsigned> > infeasibleSubsets = vector<vector<unsigned> >();
        assert( !mpPrimaryBackend->rInfeasibleSubsets().empty() );
        for( vec_set_const_pFormula::const_iterator infSubSet = mpPrimaryBackend->rInfeasibleSubsets().begin();
                infSubSet != mpPrimaryBackend->rInfeasibleSubsets().end(); ++infSubSet )
        {
            assert( !infSubSet->empty() );
            infeasibleSubsets.push_back( vector<unsigned>() );
            for( set< const Formula* >::const_iterator infSubFormula = infSubSet->begin(); infSubFormula != infSubSet->end(); ++infSubFormula )
            {
                unsigned infSubFormulaPos = 0;
                for( Formula::const_iterator subFormula = mpPrimaryBackend->rReceivedFormula().begin();
                        subFormula != mpPrimaryBackend->rReceivedFormula().end(); ++subFormula )
                {
                    if( (*subFormula)->constraint() == (*infSubFormula)->constraint() )
                    {
                        infeasibleSubsets.back().push_back( infSubFormulaPos );
                        break;
                    }
                    ++infSubFormulaPos;
                }
            }
        }
        return infeasibleSubsets;
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
        vector<ModuleFactory*> backendFactories = getBackendsFactories( _formula, _requiredBy );
        for( vector<ModuleFactory*>::const_iterator backendFactory = backendFactories.begin(); backendFactory != backendFactories.end();
                ++backendFactory )
        {
            assert( (*backendFactory)->type() != _requiredBy->type() );
            vector<Module*>::iterator backend = allBackends.begin();
            while( backend != allBackends.end() )
            {
                if( (*backend)->type() == (*backendFactory)->type() )
                {
                    // the backend already exists
                    backends.push_back( *backend );
                    break;
                }
                ++backend;
            }
            if( backend == allBackends.end() )
            {
                // backend does not exist => create it
                Module* pBackend = (*backendFactory)->create( this, _requiredBy->pPassedFormula() );
                mGeneratedModules.push_back( pBackend );
                allBackends.push_back( pBackend );
                backends.push_back( pBackend );
                // inform it about all constraints
                for( fcs_const_iterator constraint = _requiredBy->constraintsToInform().begin();
                     constraint != _requiredBy->constraintsToInform().end();
                     ++constraint )
                {
                    pBackend->inform( *constraint );
                }
            }
        }
        return backends;
    }

    /**
     * Get the module types which shall be used as backend for the module requiring backends.
     *
     * @param _formula      The problem instance.
     * @param _requiredBy   The module asking for a backend.
     *
     * @return  The module types which shall be used as backend for the module requiring backends.
     */
    vector<ModuleFactory*> Manager::getBackendsFactories( Formula* const _formula, Module* _requiredBy ) const
    {
        vector<ModuleFactory*> result = vector<ModuleFactory*>();

        /*
         * Find the first fulfilled strategy case.
         */
        vector<ModuleStrategyCase>::const_iterator strategyCase = mpStrategy->fulfilledCase( _formula );
        if( strategyCase != mpStrategy->strategy().end() )
        {
            /*
             * The first strategy case fulfilled specifies the types of the backends to return.
             */
            for( set<ModuleType>::const_iterator moduleType = strategyCase->second.begin(); moduleType != strategyCase->second.end(); ++moduleType )
            {
                result.push_back( (*mpModulFactories)[*moduleType] );
            }
        }
        return result;
    }

}    // namespace smtrat

