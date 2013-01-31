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
 * @file   PreprocessingModule.h
 *         Created on January 10, 2013, 9:59 PM
 * @author: Sebastian Junges
 *
 * 
 */

#pragma once

#include "../../Module.h"
#include <unordered_map>
#include <ginacra/datastructures/bitvector.h>

namespace smtrat
{
    struct TCall 
    {
        GiNaCRA::BitVector passedConstraints;
        unsigned nrConstraints;
    };
    
    struct TCallResponse
    {
        Answer answer;
        vec_set_const_pFormula infSubsets;
    };
    
    struct TCallHash
    {
        // TODO write a better hash (something with some bitoperations on the bitvector together with the nr of constraints.
        size_t operator() (const TCall& tcall) const
        {
            return tcall.nrConstraints;
        }
    };
    
    
    struct TCallEqual
    {
        size_t operator() (const TCall& tcall1, const TCall& tcall2) const
        {
            return (tcall1.nrConstraints == tcall2.nrConstraints && tcall1.passedConstraints == tcall2.passedConstraints);
                   
        }
    };

    class CacheModule : public Module
    {
        typedef std::unordered_map<TCall, TCallResponse, TCallHash, TCallEqual> TCallCache;
        protected:
            TCallCache mCallCache;
            
            TCall mActualTCall;
        public:
            /**
             * Constructors:
             */
            CacheModule( ModuleType, const Formula* const,  RuntimeSettings*, Manager* const _tsManager );

            /**
             * Destructor:
             */
            virtual ~CacheModule();

            /**
             * Methods:
             */

            // Interfaces.
            bool assertSubformula( Formula::const_iterator );
            Answer isConsistent();
            void removeSubformula( Formula::const_iterator );
            
            bool callCacheLookup();
            void callCacheSave();
            
            void print();
    };

}    // namespace smtrat

