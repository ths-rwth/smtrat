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
 * File:   LRAOneModule.cpp
 * @author name surname <emailadress>
 *
 * @version 2012-04-05
 * Created on April 5th, 2012, 3:22 PM
 */

#include "LRAOneModule.h"
using namespace std;

//namespace smtrat
//{
//    /**
//     * Constructor
//     */
//    LRAOneModule::LRAOneModule( Manager* const _tsManager, const Formula* const _formula ):
//        Module( _tsManager, _formula )
//    {
//        this->mModuleType = MT_LRATwoModule;
//    }
//
//    /**
//     * Destructor:
//     */
//    LRAOneModule::~LRAOneModule()
//    {
//    }
//
//    /**
//     * Methods:
//     */
//
//	/**
//     * Informs about a new constraints.
//     * @param c A new constraint
//     *
//     */
//    bool LRAOneModule::inform( const Constraint* const _constraint )
//    {
//    	return true;
//    }
//
//    /**
//     * Adds a constraint to this module.
//     *
//     * @param _constraint The constraint to add to the already added constraints.
//     *
//     * @return  true,   if the constraint and all previously added constraints are consistent;
//     *          false,  if the added constraint or one of the previously added ones is inconsistent.
//     */
//    bool LRAOneModule::assertSubFormula( const Formula* const _formula )
//    {
//        assert( _formula->getType() == REALCONSTRAINT );
//        Module::assertSubFormula( _formula );
//        return true;
//    }
//
//    /**
//     * Checks the so far received constraints for consistency.
//     *
//     * @return  True,    if the conjunction of received constraints is consistent;
//     *          False,   if the conjunction of received constraints is inconsistent;
//     *          Unknown, otherwise.
//     */
//    Answer LRAOneModule::isConsistent()
//    {
//        return True;
//    }
//
//    /**
//     * Pops the last backtrackpoint, from the stack of backtrackpoints.
//     */
//    void LRAOneModule::popBacktrackPoint()
//    {
//        Module::popBacktrackPoint();
//    }
//
//    /**
//     * Pushes a backtrackpoint, to the stack of backtrackpoints.
//     */
//    void LRAOneModule::pushBacktrackPoint()
//    {
//        Module::pushBacktrackPoint();
//    }
//
//}    // namespace smtrat