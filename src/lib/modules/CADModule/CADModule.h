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
 * @version 2013-05-27
 *
 */
#ifndef SMTRAT_CADMODULE_H
#define SMTRAT_CADMODULE_H

#include "config.h"
#include "../../solver/Module.h"
#include "../../solver/RuntimeSettings.h"

#include <unordered_map>

#include "carl/cad/CAD.h"

#include "../../datastructures/VariableBounds.h"
#ifdef SMTRAT_DEVOPTION_Statistics
#include "CADStatistics.h"
#endif

namespace smtrat
{
    /// Hash function for use of Input::const_iterator in unordered data structures
    struct FormulaIteratorHasher
    {
        size_t operator ()(ModuleInput::const_iterator i) const
        {
            return i->formula().constraint().id();
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
		typedef std::unordered_map<FormulaT, unsigned> ConstraintIndexMap;
		typedef smtrat::vb::VariableBounds< FormulaT > VariableBounds;

		////////////////
		// ATTRIBUTES //
		////////////////

		/// The actual CAD object.
		carl::CAD<smtrat::Rational> mCAD;

		/// The constraints extracted from the passed formulas.
		std::vector<carl::cad::Constraint<smtrat::Rational>> mConstraints;
        std::map<carl::cad::Constraint<smtrat::Rational>, FormulaT> mCFMap;

		/// Indicates if false has been asserted.
		bool hasFalse;
		/**
		 * If false has been asserted, new formulas are stored in this list until false is removed.
		 * This prevents unnecessary add() and remove() operation on the CAD object.
		 */
		FormulasT subformulaQueue;
		/// Maps the received formulas to indices within mConstraints.
		ConstraintIndexMap mConstraintsMap;
		
		/// A satisfying assignment of the received constraints if existent; otherwise it is empty.
		carl::RealAlgebraicPoint<smtrat::Rational> mRealAlgebraicSolution;
		/// the conflict graph storing for each last component of all sample points which constraints were satisfied by the point
		carl::cad::ConflictGraph<smtrat::Rational> mConflictGraph;
		VariableBounds mVariableBounds;

        public:

            CADModule( ModuleType _type, const ModuleInput*, RuntimeSettings*, Conditionals&, Manager* const = NULL );

            ~CADModule();

            bool addCore(ModuleInput::const_iterator _subformula);
            void removeCore(ModuleInput::const_iterator _subformula);
            Answer checkCore( bool _full = true );
            void updateModel() const;


            const VariableBounds&   variableBounds  ()	const 	{ return mVariableBounds; }
            VariableBounds&         rVariableBounds ()      	{ return mVariableBounds; }
            const ConstraintIndexMap&   constraints  ()	const 	{ return mConstraintsMap; }
            carl::cad::ConflictGraph<smtrat::Rational>   conflictGraph() const { return mConflictGraph; }
            
            const FormulaT& formulaFor(const carl::cad::Constraint<smtrat::Rational>& constraint) const {
                auto it = mCFMap.find(constraint);
                assert(it != mCFMap.end());
                return it->second;
            }

        private:
			bool addConstraintFormula(const FormulaT& f);
            const carl::cad::Constraint<smtrat::Rational> convertConstraint(const ConstraintT&);
            ConstraintT convertConstraint(const carl::cad::Constraint<smtrat::Rational>&);
            std::vector<FormulasT> extractMinimalInfeasibleSubsets_GreedyHeuristics(carl::cad::ConflictGraph<smtrat::Rational>& conflictGraph);
            const FormulaT& getConstraintAt(unsigned index);
            void updateConstraintMap(unsigned index, bool decrement = true);
#ifdef SMTRAT_DEVOPTION_Statistics
			CADStatistics* mStats;
#endif
    };

}    // namespace smtrat
#endif   /** CADMODULE_H */
