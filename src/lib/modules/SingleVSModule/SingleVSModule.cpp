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
 * SingleVSModule.cpp
 * @author Florian Corzilius
 * @since 2011-05-23
 * @version 2011-12-05
 */

#include "SingleVSModule.h"

using namespace std;
using namespace svs;

namespace smtrat
{
    /**
     * Constructor
     */
    SingleVSModule::SingleVSModule( ModuleType _type, const Formula* const _formula, RuntimeSettings* settings, Conditionals& _conditionals, Manager* const _manager ):
        Module( _type, _formula, _conditionals, _manager ),
        mNumberOfConsideredConstraints( 0 ),
        mTCRanking( TCRanking() )
    {
        this->mModuleType = MT_SingleVSModule;
    }

    /**
     * Destructor:
     */
    SingleVSModule::~SingleVSModule()
    {
        while( !mTCRanking.empty() )
        {
            TCCPair* pTccpair = mTCRanking.begin()->second;
            mTCRanking.erase( mTCRanking.begin() );
            delete pTccpair;
        }
    }

    /**
     * Methods:
     */

    /**
     * Informs about a new constraints.
     * @param c A new constraint
     *
     */
    bool SingleVSModule::inform( const Constraint* const _constraint )
    {
        return true;
    }

    /**
     * Adds a subformula to this module.
     *
     * @param _formula The subformula to add.
     *
     * @return  false,  if it can decide that the subformula is inconsistent;
     *          true,   otherwise.
     */
    bool SingleVSModule::assertSubformula( Formula::const_iterator _subformula )
    {
        assert( (*_subformula)->getType() == REALCONSTRAINT );
        Module::assertSubformula( _subformula );
        return true;
    }

    /**
     * Checks the so far received subformulas for consistency.
     *
     * @return  True,    if the conjunction of received subformulas is consistent;
     *          False,   if the conjunction of received subformulas is inconsistent;
     *          Unknown, otherwise.
     */
    Answer SingleVSModule::isConsistent()
    {
        //        for( ; mNumberOfComparedConstraints < receivedFormulaSize(); ++mNumberOfComparedConstraints )
        //        {
        //            const Formula* receivedFormula = receivedFormulaAt( mNumberOfComparedConstraints );
        //            Formula* subresult =
        //            addReceivedSubformulaToPassedFormula( mNumberOfComparedConstraints );
        //        }
        return foundAnswer( Unknown );
    }

    /**
     * Removes a everything related to a sub formula of the received formula.
     *
     * @param _subformula The sub formula of the received formula to remove.
     */
    void SingleVSModule::removeSubformula( Formula::const_iterator _subformula )
    {
        Module::removeSubformula( _subformula );
    }
}    // namespace smtrat

