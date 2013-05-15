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
 * @file   CADModule.h
 *
 * @author Ulrich Loup
 * @since 2012-02-04
 * @version 2013-05-15
 *
 */
#ifndef SMTRAT_CADMODULE_H
#define SMTRAT_CADMODULE_H



#include "config.h"
#include "../../Module.h"
#include "../../RuntimeSettings.h"

#include <unordered_map>
#include <ginac/ginac.h>
#include <ginacra/ginacra.h>

#ifdef SMTRAT_CAD_VARIABLEBOUNDS
#include "../../VariableBounds.h"
#endif

namespace smtrat
{
    /// Hash function for use of Formula::const_iterator in unordered data structures
    struct FormulaIteratorHasher
    {
        size_t operator ()( Formula::const_iterator i ) const
        {
            return (*i)->pConstraint()->id();
        }
    };

    /**
     * Module invoking a CAD solver of the GiNaCRA library. The solver is only used with univariate polynomials.
     * If a polynomial with more than one variable is added, this module passes it on.
     *
     * @author Ulrich Loup
     * @since 2012-02-04
     * @version 2012-11-29
     *
     */
    class CADModule:
        public Module
    {
        typedef std::unordered_map<Formula::const_iterator, unsigned, FormulaIteratorHasher> ConstraintIndexMap;
        #ifdef SMTRAT_CAD_VARIABLEBOUNDS
        typedef smtrat::vb::VariableBounds< Formula > VariableBounds;
        #endif

        ////////////////
        // ATTRIBUTES //
        ////////////////

        /// representation of the solution space containing all data relevant for CAD computations
        GiNaCRA::CAD mCAD;
        /// the GiNaCRA constraints
        vector<GiNaCRA::Constraint> mConstraints;
        /// the GiNaCRA constraints' indices assigned to the received constraints
        ConstraintIndexMap mConstraintsMap;
        /// a satisfying assignment of the received constraints if existent; otherwise it is empty
        GiNaCRA::RealAlgebraicPoint mRealAlgebraicSolution;
        /// the conflict graph storing for each last component of all sample points which constraints were satisfied by the point
        GiNaCRA::ConflictGraph mConflictGraph;
        #ifdef SMTRAT_CAD_VARIABLEBOUNDS
        VariableBounds mVariableBounds;
        #endif

        public:

            /// Stores the internal (GiNaC) variable names representing the roots of univariate polynomials discovered by any CAD module
            static std::map<std::string,std::pair<std::string,GiNaC::ex> > mRootVariables;

            CADModule( ModuleType _type, const Formula* const, RuntimeSettings*, Conditionals&, Manager* const = NULL );

            virtual ~CADModule();

            virtual bool assertSubformula( Formula::const_iterator _subformula );
            virtual void removeSubformula( Formula::const_iterator _subformula );
            virtual Answer isConsistent();
            void updateModel();


            #ifdef SMTRAT_CAD_VARIABLEBOUNDS
            const VariableBounds&   variableBounds  ()	const 	{ return mVariableBounds; }
            VariableBounds&         rVariableBounds ()      	{ return mVariableBounds; }
            #endif

        private:
            const GiNaCRA::Constraint convertConstraint( const Constraint& );
            const Constraint* convertConstraint( const GiNaCRA::Constraint& );
            vec_set_const_pFormula extractMinimalInfeasibleSubsets_GreedyHeuristics( GiNaCRA::ConflictGraph conflictGraph );
            void addDeductions( const list<pair<list<GiNaCRA::Constraint>, list<GiNaCRA::Constraint> > >& deductions );
            const Formula* getConstraintAt( unsigned index );
            void updateConstraintMap( unsigned index, bool decrement = true );
    };

}    // namespace smtrat
#endif   /** CADMODULE_H */
