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
 * @file BVModule.tpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-02-05
 * Created on 2015-02-05.
 */

#include "BVModule.h"

namespace smtrat
{
    /**
     * Constructors.
     */

    template<class Settings>
    BVModule<Settings>::BVModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        Module( _type, _formula, _conditionals, _manager )
    {}

    /**
     * Destructor.
     */

    template<class Settings>
    BVModule<Settings>::~BVModule()
    {}


    template<class Settings>
    bool BVModule<Settings>::informCore( const FormulaT& _constraint )
    {
        const smtrat::ConstraintT& constraint = _constraint.constraint(); // Constraint pointer for the passed formula.
        return constraint.isConsistent() != 0;
    }

    template<class Settings>
    void BVModule<Settings>::init()
    {}

    template<class Settings>
    bool BVModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        // Your code.
        return true; // This should be adapted according to your implementation.
    }

    template<class Settings>
    void BVModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
        // Your code.
    }

    template<class Settings>
    void BVModule<Settings>::updateModel() const
    {
        clearModel();
        if(solverState() == True)
        {
            getBackendsModel();
        }
    }

    template<class Settings>
    Answer BVModule<Settings>::checkCore( bool _full )
    {
        auto receivedSubformula = firstUncheckedReceivedSubformula();
        while(receivedSubformula != rReceivedFormula().end())
        {
            const FormulaWithOrigins& fwo = *receivedSubformula;
            const FormulaT& formula = fwo.formula();

            std::cerr << "[BVModule] Encoding formula:" << std::endl << " -(IN ): " << formula << std::endl;

            const FormulasT& formulasToPass = mEncoder.encode(formula);

            for(const FormulaT formulaToPass : formulasToPass)
            {
                std::cerr << " -(OUT): " << formulaToPass << std::endl;
                addSubformulaToPassedFormula(formulaToPass, formula);
            }
            ++receivedSubformula;
        }

        Answer backendAnswer = runBackends(_full);
        if(backendAnswer == False)
        {
            getInfeasibleSubsets();
        }

        return backendAnswer;
    }
}
