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
 * @file UVariable.h
 * @author Florian Corzilius
 * @since 2014-10-20
 * @version 2014-10-22
 */

#pragma once

#include "Common.h"
#include "Sort.h"
#include "SortManager.h"

namespace smtrat
{
    /**
     * Implements an uninterpreted variable.
     */
    class UVariable
    {
        private:
            
            // Members.
            
            /// The according carl::variable, hence, the actual content of this class.
            carl::Variable mVar;
            /// The domain.
            Sort mDomain;
            
        public:
			/**
			 * Default constructor.
			 * The resulting object will not be a valid variable, but a dummy object.
             */
            UVariable(): mVar(carl::Variable::NO_VARIABLE) {
			}

			UVariable( carl::Variable::Arg _var):
                mVar( _var ),
				mDomain( SortManager::getInstance().interpretedSort(_var.getType()) )
            {
			}
            
            /**
             * Constructs an uninterpreted variable.
             * @param _var The carl::variable of the uninterpreted variable to construct.
             * @param _domain The domain of the uninterpreted variable to construct.
             */
            UVariable( carl::Variable::Arg _var, Sort _domain ):
                mVar( _var ),
                mDomain( _domain )
            {}
            
            /**
             * @return The according carl::variable, hence, the actual content of this class.
             */
            carl::Variable operator()() const 
            {
                return mVar;
            }
            
            /**
             * @return The domain of this uninterpreted variable.
             */
            const Sort& domain() const
            {
                return mDomain;
            }
            
            /**
             * @param _uvar The uninterpreted variable to compare with.
             * @return true, if this and the given uninterpreted variable are equal.
             */
            bool operator==( const UVariable& _uvar ) const
            {
                return mVar == _uvar();
            }
            
            /**
             * @param _uvar The uninterpreted variable to compare with.
             * @return true, if this uninterpreted variable is less than the given one.
             */
            bool operator<( const UVariable& _uvar ) const
            {
                return mVar < _uvar();
            }
            
            /**
             * Prints the given uninterpreted variable on the given output stream.
             * @param _os The output stream to print on.
             * @param _uvar The uninterpreted variable to print.
             * @return The output stream after printing the given uninterpreted variable on it.
             */
            friend std::ostream& operator<<( std::ostream& _os, const UVariable& _uvar )
            {
                return (_os << _uvar());
            }
    };
} // end namespace smtrat

namespace std
{
    /**
     * Implements std::hash for uninterpreted variables.
     */
    template<>
    struct hash<smtrat::UVariable>
    {
    public:
        /**
         * @param _uvar The uninterpreted variable to get the hash for.
         * @return The hash of the given uninterpreted variable.
         */
        size_t operator()( const smtrat::UVariable& _uvar ) const 
        {
            return hash<carl::Variable>()( _uvar() ) ;
        }
    };
}
