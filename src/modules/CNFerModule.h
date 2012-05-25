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

/*
 * File:   CNFTransformerModule.h
 * Author: Florian Corzilius
 *
 * Created on 02. May 2012, 20:53
 */

#ifndef SMTRAT_CNFERMODULE_H
#define SMTRAT_CNFERMODULE_H

#include "../Module.h"

namespace smtrat
{
    class CNFerModule:
        public Module
    {
        private:
            /**
             * Members.
             */
            bool mFixedTheModuleID;
            unsigned mModuleID;
            std::vector< unsigned > mAuxVarCounterHistory;
        public:
            /**
             * Constructor and destructor.
             */
            CNFerModule( Manager* const _tsManager, const Formula* const _formula );

            ~CNFerModule();

            /**
             * Methods:
             */

            // Interfaces.
            bool assertSubFormula( const Formula* const );
            Answer isConsistent();
            void pushBacktrackPoint();
            void popBacktrackPoint();


            /**
             * Generates a fresh Boolean variable and returns its identifier.
             *
             * @return The identifier of a fresh Boolean variable.
             */
            std::string getFreeBooleanIdentifier()
            {
                // TODO: A name which definitely does not already appear in the formula.
                assert( !mAuxVarCounterHistory.empty() );
                if( !mFixedTheModuleID )
                {
                    mModuleID = mpTSManager->uniqueModuleNumber( this );
                    mFixedTheModuleID = true;
                }
                std::stringstream out;
                out << "h_" << mModuleID << "_" << mAuxVarCounterHistory.back()++;
                return out.str();
            }

        private:
            /**
             * Methods:
             */
            bool assertClauses( std::vector< Formula* >&, vec_set_const_pFormula& );
            Formula* resolveNegation( Formula* ) const;
            void printSolverState( const std::vector< Formula* >& ) const;
    };

}    // namespace smtrat
#endif   /** CNFTRANSFORMERMODULE_H */
