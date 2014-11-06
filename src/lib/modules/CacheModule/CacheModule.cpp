/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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
 * @file   VRWModule.cpp
 * @author: Sebastian Junges
 *
 *
 */

#include "CacheModule.h"
#include "../../../cli/ExitCodes.h"


#define CACHE_ONLY_TRUE
using namespace smtrat::cachemodule;

namespace smtrat
{
    CacheModule::CacheModule( ModuleType _type, const FormulaT* const _formula, RuntimeSettings* settings, Conditionals& _conditionals, Manager* const _manager ):
        Module( _type, _formula, _conditionals, _manager )
    {}

    /**
     * Destructor:
     */
    CacheModule::~CacheModule(){}

    /**
     * Methods:
     */

    /**
     * Adds a constraint to this module.
     *
     * @param _constraint The constraint to add to the already added constraints.
     *
     * @return true
     */
    bool CacheModule::assertSubformula( FormulaT::const_iterator _subformula )
    {
        Module::assertSubformula( _subformula );
        addReceivedSubformulaToPassedFormula(_subformula);
        assert((*_subformula)->getType() == CONSTRAINT);
        ++(mActualTCall.nrConstraints);
        assert(mActualTCall.passedConstraints.getBit((*_subformula)->pConstraint()->id()) == false);
        mActualTCall.passedConstraints.setBit((*_subformula)->pConstraint()->id(), true);
        return true;
    }

    /**
     * Checks the so far received constraints for consistency.
     */
    Answer CacheModule::isConsistent()
    {
        if(callCacheLookup())
        {

        }
        else
        {
            Answer ans = runBackends();
            if( ans == False )
            {
                getInfeasibleSubsets();
            }

            callCacheSave();
            foundAnswer( ans );
        }
        return solverState();
    }

    /**
     * Removes a everything related to a sub formula of the received formula.
     *
     * @param _subformula The sub formula of the received formula to remove.
     */
    void CacheModule::removeSubformula( FormulaT::const_iterator _subformula )
    {
        --(mActualTCall.nrConstraints);
        assert(mActualTCall.passedConstraints.getBit((*_subformula)->pConstraint()->id()) == true);
        mActualTCall.passedConstraints.setBit((*_subformula)->pConstraint()->id(), false);
        Module::removeSubformula( _subformula );
    }

    bool CacheModule::callCacheLookup()
    {
        TCallCache::const_iterator value = mCallCache.find(mActualTCall);
        if(value != mCallCache.end())
        {
            //std::cout << "Cache hit: ";
            foundAnswer( value->second.answer );
            #ifdef CACHE_ONLY_TRUE
            assert(solverState() == True);
            #else
            if(solverState() == False)
            {
                return false;
                //mInfeasibleSubsets = value->second.infSubsets;
            }
            #endif
            return true;
        }
        return false;
    }

    void CacheModule::callCacheSave()
    {
        TCallResponse response;
        response.answer = solverState();
#ifdef CACHE_ONLY_TRUE
        if(response.answer == True)
        {
            mCallCache.insert(std::pair<TCall, TCallResponse>(mActualTCall, response));
        }
#else
        if(response.answer == False)
        {
            response.infSubsets = mInfeasibleSubsets;
        }
        mCallCache.insert(std::pair<TCall, TCallResponse>(mActualTCall, response));
#endif

    }

    void CacheModule::printCache()
    {
        std::cout << "actual call:" << std::endl;
        mActualTCall.passedConstraints.print();

        std::cout << "call cache:" << std::endl;
        for(TCallCache::const_iterator it = mCallCache.begin(); it != mCallCache.end(); ++it )
        {
            it->first.passedConstraints.print();
            std::cout << " --> " << it->second.answer << std::endl;
        }
    }
}