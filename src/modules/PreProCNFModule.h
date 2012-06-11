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
 * File:   PreProCNFModule.h
 * Author: Dennis Scully
 *
 * Created on 15. May 2012, 14:14
 */

#ifndef SMTRAT_PreProCNFModule_H
#define SMTRAT_PreProCNFModule_H

#include "../Module.h"
#include <ginac/ginac.h>
#include <ginac/flags.h>
#include <vector>

namespace smtrat
{
    class PreProCNFModule:
        public Module
    {
        public:

            /**
             * Constructors:
             */
            PreProCNFModule( Manager* const _tsManager, const Formula* const _formula );

            /**
             * Destructor:
             */
            virtual ~PreProCNFModule();

            /**
             * Methods:
             */

            // Interfaces.
            bool assertSubFormula( const Formula* const );
            Answer isConsistent();
            std::pair< const Formula*, const Formula* > isCandidate( const Formula* const ) const;
            bool substituteConstraint( const Formula* const, std::pair< std::pair< std::string, bool >,
                    std::pair< std::pair<GiNaC::symtab, GiNaC::symtab>, std::pair< GiNaC::ex, GiNaC::ex> > >,
                    vec_set_const_pFormula );
            void popBacktrackPoint();
            void pushBacktrackPoint();

        private:

            bool                                                                mNewFormulaReceived;
            unsigned                                                            mNumberOfCheckedFormulas;
            std::vector< vec_set_const_pFormula >                               mSubstitutionOrigins;
            std::map< std::string, unsigned >                                     mNumberOfVariables;
            std::vector< std::pair< std::pair< std::string, bool >, std::pair< std::pair<GiNaC::symtab, GiNaC::symtab>, std::pair< GiNaC::ex, GiNaC::ex> > > >    mSubstitutions;
            std::vector< std::pair< std::vector< std::pair< Formula*, vec_set_const_pFormula > >, std::pair < bool, std::pair< unsigned, unsigned> > > >    mBacktrackPoints;
                                                                                          // mBacktrackPoints saves all requiered data
                                                                                          // Subformulas + Origins + mNewFormulaReceived
                                                                                          // + mNumberOfCheckedFormulas + NumberOfKnownSubstitutions



    };

}    // namespace smtrat
#endif   /** PreProCNFModule_H */
