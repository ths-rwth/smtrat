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
 * @file UIVariable.h
 * @author Florian Corzilius
 * @since 2014-10-20
 * @version 2014-10-20
 */

#pragma once

#include "Common.h"
#include "Sort.h"

namespace smtrat
{
    class UIVariable
    {
        private:
            
            // Members.
            
            ///
            carl::Variable mVar;
            ///
            Sort mDomain;
            
        public:
            
            UIVariable(); // No default constructor.
            
            /**
             * 
             * @param _var
             * @param _domain
             */
            UIVariable( carl::Variable::Arg _var, Sort _domain ):
                mVar( _var ),
                mDomain( _domain )
            {}
            
            carl::Variable operator()() const 
            {
                return mVar;
            }
            
            const Sort& domain() const
            {
                return mDomain;
            }
            
            bool operator==( const UIVariable& _uvar ) const
            {
                return mVar == _uvar();
            }
            
            bool operator!=( const UIVariable& _uvar ) const
            {
                return mVar != _uvar();
            }
            
            bool operator<( const UIVariable& _uvar ) const
            {
                return mVar < _uvar();
            }
            
            bool operator>( const UIVariable& _uvar ) const
            {
                return mVar > _uvar();
            }
    };
} // end namespace smtrat

namespace std
{
    /**
     * Implements std::hash for uninterpreted variables.
     */
    template<>
    struct hash<smtrat::UIVariable>
    {
    public:
        /**
         * @param _ueq The uninterpreted variable to get the hash for.
         * @return The hash of the given uninterpreted variable.
         */
        size_t operator()( const smtrat::UIVariable& _uvar ) const 
        {
            return hash<carl::Variable>()( _uvar() ) ;
        }
    };
}
