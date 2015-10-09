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
 *
 * @version 2015-02-05
 * Created on 2015-02-05.
 */

#include "BVModule.h"
#include <limits>

namespace smtrat
{
    /**
     * Constructors.
     */

    template<class Settings>
    BVModule<Settings>::BVModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        Module( _type, _formula, _conditionals, _manager ),
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
        if( _subformula->formula().isFalse() )
        {
            receivedFormulasAsInfeasibleSubset( _subformula );
            return false;
        }
        if( Settings::incremental_flattening )
        {
            auto sortKey = std::make_pair( evaluateBVFormula(_subformula->formula()), _subformula->formula().getId() );
            std::cout << std::endl << std::endl << "add formula" << std::endl;
            std::cout << _subformula->formula() << std::endl;
            std::cout << "Evaluation: " << sortKey << std::endl;
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
                std::cout << std::endl << std::endl << "remove formula" << std::endl;
                std::cout << _subformula->formula() << std::endl;
                mBlastedFormulas.erase( iterA );
            }
            else
            {
                std::cout << std::endl << std::endl << "remove formula" << std::endl;
                std::cout << _subformula->formula() << std::endl;
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
        if(solverState() == True)
        {
            getBackendsModel();
        }

        // Build bitvector values from the values of the single bits
        auto& blastings = mEncoder.bitvectorBlastings();

        for(auto const & bitvectorToBits : blastings)
        {
            carl::BVValue composedValue(bitvectorToBits.first.width());

            for(std::size_t i=0;i<bitvectorToBits.second.size();++i)
            {
                composedValue[i] = mModel[bitvectorToBits.second[i]].asBool();
            }

            mModel[bitvectorToBits.first] = composedValue;
        }

        // Remove internal variables which have been introduced by blasting
        auto& introducedVariables = mEncoder.introducedVariables();

        for(auto const & introducedVariable : introducedVariables)
        {
            mModel.erase(introducedVariable);
        }
    }

    template<class Settings>
    Answer BVModule<Settings>::checkCore( bool _full )
    {
        if( Settings::incremental_flattening )
        {
            std::cout << "Check in BVModule" << std::endl;
            carl::Variables allVars;
            rReceivedFormula().vars( allVars );
            auto allVarsIter = allVars.begin();
            auto oldModelIter = mModel.begin();
            while( allVarsIter != allVars.end() && oldModelIter != mModel.end() )
            {
                ModelVariable mv( *allVarsIter );
                if( mv == oldModelIter->first )
                {
                    ++allVarsIter;
                    ++oldModelIter;
                }
                else if( mv < oldModelIter->first )
                {
                    oldModelIter = mModel.insert( oldModelIter, std::make_pair( mv, 0 ) );
                    ++oldModelIter;
                    ++allVarsIter;
                }
                else
                {
                    oldModelIter = mModel.erase( oldModelIter );
                }
            }
            if( oldModelIter != mModel.end() )
                mModel.erase( oldModelIter, mModel.end() );
            else
            {
                for( ; allVarsIter != allVars.end(); ++allVarsIter )
                    mModel.insert( mModel.end(), std::make_pair( ModelVariable(*allVarsIter), 0 ) );
            }
            std::cout << "initial model:" << std::endl;
            std::cout << mModel << std::endl << std::endl;
            if( !mFormulasToBlast.empty() )
            {
                FormulaT origin = mFormulasToBlast.begin()->second;
                std::cout << std::endl << std::endl << "Take into account: " << std::endl;
                std::cout << origin << std::endl;
                const FormulaSetT& formulasToPass = mEncoder.encode( origin );
                mFormulasToBlast.erase( mFormulasToBlast.begin() );
                for( const FormulaT& formulaToPass : formulasToPass )
                    addSubformulaToPassedFormula( formulaToPass, origin );
            }
            while( !mFormulasToBlast.empty() )
            {
                std::cout << std::endl << "Run backends" << std::endl;
                Answer backendAnswer = runBackends(_full);
                std::cout << " --> " << ANSWER_TO_STRING(backendAnswer) << std::endl << std::endl;
                switch( backendAnswer )
                {
                    case False:
                    {
                        getInfeasibleSubsets();
                        return False;
                    }
                    case True:
                    {
                        updateModel();
                        Model currentModel = model();
                        std::cout << "current model: " << std::endl;
                        std::cout << currentModel << std::endl;
                        FormulaT nextFormulaToAdd( carl::FormulaType::TRUE );
                        std::pair<size_t,size_t> bestEvaluation = std::make_pair( std::numeric_limits<size_t>::max(), std::numeric_limits<size_t>::max() );
                        EvalRationalMap rationalAssigns;
                        getRationalAssignmentsFromModel( currentModel, rationalAssigns );
                        for( const auto& rf : rReceivedFormula() )
                        {
                            if( mBlastedFormulas.find( rf.formula() ) != mBlastedFormulas.end() )
                            {
                                std::cout << __LINE__ << std::endl;
                                continue;
                            }
                            if( !nextFormulaToAdd.isTrue() )
                            {
                                std::cout << __LINE__ << std::endl;
                                auto iter = mPositionInFormulasToBlast.find( rf.formula() );
                                assert( iter != mPositionInFormulasToBlast.end() );
                                if( iter->second->first >= bestEvaluation )
                                {
                                    std::cout << __LINE__ << std::endl;
                                    continue;
                                }
                            }
                            unsigned tmp = satisfies( currentModel, rationalAssigns, rf.formula() );
                            std::cout << "satisfies( currentModel, rationalAssigns, rf.formula() ) = " << tmp << std::endl; 
                            assert( tmp != 2 );
                            if( tmp == 0 )
                            {
                                std::cout << __LINE__ << std::endl;
                                std::cout << std::endl << std::endl << "Not yet satisfied: " << std::endl;
                                std::cout << rf.formula() << std::endl;
                                auto iter = mPositionInFormulasToBlast.find( rf.formula() );
                                assert( iter != mPositionInFormulasToBlast.end() );
                                if( iter->second->first < bestEvaluation )
                                {
                                    std::cout << __LINE__ << std::endl;
                                    nextFormulaToAdd = iter->second->second;
                                    bestEvaluation = iter->second->first;
                                }
                            }
                        }
                        if( nextFormulaToAdd.isTrue() )
                        {
                            std::cout << __LINE__ << std::endl;
                            return True;
                        }
                        else
                        {
                            std::cout << __LINE__ << std::endl;
                            assert( !nextFormulaToAdd.isFalse() );
                            const FormulaSetT& formulasToPass = mEncoder.encode( nextFormulaToAdd );
                            std::cout << std::endl << std::endl << "Take into account: " << std::endl;
                            std::cout << nextFormulaToAdd << std::endl;
                            auto iter = mPositionInFormulasToBlast.find( nextFormulaToAdd );
                            mFormulasToBlast.erase( iter->second );
                            mPositionInFormulasToBlast.erase( iter );
                            for( const FormulaT& formulaToPass : formulasToPass )
                                addSubformulaToPassedFormula( formulaToPass, nextFormulaToAdd );
                        }
                        break;
                    }
                    default:
                        assert( backendAnswer == Unknown );
                        return Unknown;
                }
            }
            assert( false ); 
            return True;
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

            Answer backendAnswer = runBackends(_full);
            if(backendAnswer == False)
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
