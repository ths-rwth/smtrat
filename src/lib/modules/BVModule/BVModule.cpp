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
 * @author Andreas Krueger <andreas.krueger@rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-02-05
 * Created on 2015-02-05.
 */

#include "BVModule.h"
#include <limits>

//#define DEBUG_BVMODULE

namespace smtrat
{
    /**
     * Constructors.
     */

    template<class Settings>
    BVModule<Settings>::BVModule( const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        Module( _formula, _conditionals, _manager ),
        mModelComputed( true ),
        mEncoder(),
        mBlastedFormulas(),
        mPositionInFormulasToBlast(),
        mFormulasToBlast()
    {}

    /**
     * Destructor.
     */

    template<class Settings>
    BVModule<Settings>::~BVModule()
    {}


    template<class Settings>
    bool BVModule<Settings>::informCore( const FormulaT& /* _constraint */ )
    {
        return true;
    }

    template<class Settings>
    void BVModule<Settings>::init()
    {}

    template<class Settings>
    bool BVModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        if( _subformula->formula().isTrue() )
            return true;
        mModelComputed = false;
        if( _subformula->formula().isFalse() )
        {
            receivedFormulasAsInfeasibleSubset( _subformula );
            return false;
        }
        if( Settings::incremental_flattening )
        {
            auto sortKey = std::make_pair( evaluateBVFormula(_subformula->formula()), _subformula->formula().getId() );
            #ifdef DEBUG_BVMODULE
            std::cout << std::endl << std::endl << "add formula" << std::endl;
            std::cout << _subformula->formula() << std::endl;
            std::cout << "Evaluation: " << sortKey << std::endl;
            #endif
            auto ret = mFormulasToBlast.insert( std::make_pair(sortKey, _subformula->formula() ) );
            assert( ret.second );
            assert( mPositionInFormulasToBlast.find( _subformula->formula() ) == mPositionInFormulasToBlast.end() );
            mPositionInFormulasToBlast[_subformula->formula()] = ret.first;
        }
        return true;
    }

    template<class Settings>
    void BVModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
        if( Settings::incremental_flattening )
        {
            auto iterA = mBlastedFormulas.find( _subformula->formula() );
            if( iterA != mBlastedFormulas.end() )
            {
                #ifdef DEBUG_BVMODULE
                std::cout << std::endl << std::endl << "remove formula" << std::endl;
                std::cout << _subformula->formula() << std::endl;
                #endif
                mBlastedFormulas.erase( iterA );
            }
            else
            {
                #ifdef DEBUG_BVMODULE
                std::cout << std::endl << std::endl << "remove formula" << std::endl;
                std::cout << _subformula->formula() << std::endl;
                #endif
                auto iterB = mPositionInFormulasToBlast.find( _subformula->formula() );
                assert( iterB != mPositionInFormulasToBlast.end() );
                mFormulasToBlast.erase( iterB->second );
                mPositionInFormulasToBlast.erase( iterB );
            }
        }
    }

    template<class Settings>
    void BVModule<Settings>::updateModel() const
    {
        if( solverState() != SAT )
            return;
        if( !Settings::incremental_flattening || !mModelComputed )
        {
            transferBackendModel();
        }
        if( Settings::incremental_flattening && !mModelComputed )
            mModelComputed = true;
    }
    

    template<class Settings>
    void BVModule<Settings>::transferBackendModel() const
    {
        clearModel();
        const Model& bModel = backendsModel();
        // Build bitvector values from the values of the single bits
        auto& blastings = mEncoder.bitvectorBlastings();

        for(auto const & bitvectorToBits : blastings)
        {
            carl::BVValue composedValue(bitvectorToBits.first.width());

            for(std::size_t i=0;i<bitvectorToBits.second.size();++i)
            {
                auto iter = bModel.find( bitvectorToBits.second[i] );
                assert( iter != bModel.end() );
                composedValue[i] = iter->second.asBool();
            }
            mModel.emplace(bitvectorToBits.first, composedValue);
        }
        if( rReceivedFormula().containsBooleanVariables() )
        {
            carl::Variables bvars;
            rReceivedFormula().booleanVars( bvars );
            auto modelIter = mModel.begin();
            for( carl::Variable::Arg var : bvars )
            {
                auto bmodelIter = bModel.find( var );
                assert( bmodelIter != bModel.end() );
                modelIter = mModel.emplace_hint( modelIter, var, bmodelIter->second.asBool() );
            }
        }
    }

    template<class Settings>
    Answer BVModule<Settings>::checkCore()
    {
        if( Settings::incremental_flattening )
        {
            #ifdef DEBUG_BVMODULE
            std::cout << "Check in BVModule" << std::endl;
            #endif
            getDefaultModel( mModel, (FormulaT) rReceivedFormula() );
            #ifdef DEBUG_BVMODULE
            std::cout << "initial model:" << std::endl;
            std::cout << mModel << std::endl << std::endl;
            #endif
            if( !mFormulasToBlast.empty() )
            {
                FormulaT origin = mFormulasToBlast.begin()->second;
                #ifdef DEBUG_BVMODULE
                std::cout << std::endl << std::endl << "Take into account: " << std::endl;
                std::cout << origin << std::endl;
                #endif
                const FormulaSetT& formulasToPass = mEncoder.encode( origin );
                mFormulasToBlast.erase( mFormulasToBlast.begin() );
                for( const FormulaT& formulaToPass : formulasToPass )
                    addSubformulaToPassedFormula( formulaToPass, origin );
            }
            while( true )
            {
                #ifdef DEBUG_BVMODULE
                std::cout << std::endl << "Run backends" << std::endl;
                #endif
                Answer backendAnswer = runBackends();
                #ifdef DEBUG_BVMODULE
                std::cout << " --> " << backendAnswer << std::endl << std::endl;
                #endif
                switch( backendAnswer )
                {
                    case UNSAT:
                    {
                        getInfeasibleSubsets();
                        return UNSAT;
                    }
                    case SAT:
                    {
                        transferBackendModel();
                        const Model& currentModel = model();
                        #ifdef DEBUG_BVMODULE
                        std::cout << "current model: " << std::endl;
                        std::cout << currentModel << std::endl;
                        #endif
                        auto iter = mFormulasToBlast.begin();
                        for( ; iter != mFormulasToBlast.end(); ++iter )
                        {
                            unsigned tmp = satisfies( currentModel, iter->second );
                            #ifdef DEBUG_BVMODULE
                            std::cout << "currentModel satisfies" << std::endl << iter->second << std::endl << "  ->  " << tmp << std::endl;
                            #endif
                            assert( tmp != 2 );
                            if( tmp == 0 )
                            {
                                #ifdef DEBUG_BVMODULE
                                std::cout << std::endl << std::endl << "Not yet satisfied: " << std::endl;
                                std::cout << iter->second << std::endl;
                                #endif
                                break;
                            }
                        }
                        if( iter == mFormulasToBlast.end() )
                        {
                            #ifdef DEBUG_BVMODULE
                            std::cout << "All formulas satisfied!" << std::endl;
                            #endif
                            mModelComputed = true;
                            return SAT;
                        }
                        else
                        {
                            #ifdef DEBUG_BVMODULE
                            std::cout << std::endl << std::endl << "Take into account: " << std::endl;
                            std::cout << iter->second << std::endl;
                            #endif
                            const FormulaSetT& formulasToPass = mEncoder.encode( iter->second );
                            for( const FormulaT& formulaToPass : formulasToPass )
                                addSubformulaToPassedFormula( formulaToPass, iter->second );
                            mPositionInFormulasToBlast.erase( iter->second );
                            mFormulasToBlast.erase( iter );
                        }
                        break;
                    }
                    default:
                        assert( backendAnswer == UNKNOWN );
                        return UNKNOWN;
                }
            }
            assert( false ); 
            return SAT;
        }
        else
        {
            auto receivedSubformula = firstUncheckedReceivedSubformula();
            while(receivedSubformula != rReceivedFormula().end())
            {
                const FormulaWithOrigins& fwo = *receivedSubformula;
                const FormulaT& formula = fwo.formula();

                const FormulaSetT& formulasToPass = mEncoder.encode(formula);

                for(const FormulaT& formulaToPass : formulasToPass)
                    addSubformulaToPassedFormula(formulaToPass, formula);
                ++receivedSubformula;
            }

            Answer backendAnswer = runBackends();
            if(backendAnswer == UNSAT)
            {
                getInfeasibleSubsets();
            }

            return backendAnswer;
        }
    }
    
    template<class Settings>
    size_t BVModule<Settings>::evaluateBVFormula( const FormulaT& _formula )
    {
        if( _formula.getType() == carl::FormulaType::CONSTRAINT && _formula.constraint().relation() == carl::Relation::EQ )
            return _formula.complexity();
        return Settings::equation_preference_weight * _formula.complexity();
    }
}

#include "Instantiation.h"
