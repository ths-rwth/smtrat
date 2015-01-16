/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2013 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT. If not, see <http://www.gnu.org/licenses/>.
 *
 */
/**
 * @file ModuleInput.cpp
 *
 * @author   Florian Corzilius
 * @version: 2014-05-16
 */

#include "ModuleInput.h"

using namespace std;
using namespace carl;

// Main smtrat namespace.
namespace smtrat
{   
    unsigned ModuleInput::satisfiedBy( const EvalRationalMap& _assignment ) const
    {
        unsigned result = 1;
        for( const FormulaWithOrigins& fwo : *this )
        {
            switch( fwo.formula().satisfiedBy( _assignment ) )
            {
                case 0:
                    return 0;
                case 1:
                    break;
                default:
                    if( result != 2 ) result = 2;
            }
        }
        return result;
    }
    
    unsigned ModuleInput::satisfiedBy( const Model& _assignment ) const
    {
        EvalRationalMap rationalAssigns;
        getRationalAssignmentsFromModel( _assignment, rationalAssigns );
        unsigned result = 1;
        for( const FormulaWithOrigins& fwo : *this )
        {
            switch( satisfies( _assignment, rationalAssigns, fwo.formula() ) )
            {
                case 0:
                    return 0;
                case 1:
                    break;
                default:
                    if( result != 2 ) result = 2;
            }
        }
        return result;
    }
        
    ModuleInput::iterator ModuleInput::find( const FormulaT& _formula )
    {
        #ifdef MODULE_INPUT_USE_HASHING_FOR_FIND
        auto res = mFormulaPositionMap.find( _formula );
        if( res == mFormulaPositionMap.end() )
        {
            return end();
        }
        else
        {
            return res->second;
        }
        #else
        return find( begin(), end(), _formula );
        #endif
    }

    ModuleInput::const_iterator ModuleInput::find( const FormulaT& _formula ) const
    {
        #ifdef MODULE_INPUT_USE_HASHING_FOR_FIND
        auto res = mFormulaPositionMap.find( _formula );
        if( res == mFormulaPositionMap.end() )
        {
            return end();
        }
        else
        {
            return res->second;
        }
        #else
        return std::find( begin(), end(), _formula );
        #endif
    }

    #ifdef MODULE_INPUT_USE_HASHING_FOR_FIND
    ModuleInput::iterator ModuleInput::find( const_iterator, const FormulaT& _formula )
    {
        auto res = mFormulaPositionMap.find( _formula );
        if( res == mFormulaPositionMap.end() )
        {
            return end();
        }
        else
        {
            return res->second;
        }
    }
    #else
    ModuleInput::iterator ModuleInput::find( const_iterator _hint, const FormulaT& _formula )
    {
        return std::find( _hint, end(), _formula );
    }
    #endif

    #ifdef MODULE_INPUT_USE_HASHING_FOR_FIND
    ModuleInput::const_iterator ModuleInput::find( const_iterator, const FormulaT& _formula ) const
    {
        auto res = mFormulaPositionMap.find( _formula );
        if( res == mFormulaPositionMap.end() )
        {
            return end();
        }
        else
        {
            return res->second;
        }
    }
    #else
    ModuleInput::const_iterator ModuleInput::find( const_iterator _hint, const FormulaT& _formula ) const
    {
        return std::find( _hint, end(), _formula );
    }
    #endif
    
    ModuleInput::iterator ModuleInput::erase( iterator _formula )
    {
        assert( _formula != end() );
        #ifdef MODULE_INPUT_USE_HASHING_FOR_FIND
        mFormulaPositionMap.erase( _formula->formula() );
        #endif
        return super::erase( _formula );
    }

    bool ModuleInput::removeOrigin( iterator _formula, const FormulaT& _origin )
    {
        assert( _formula != end() );
        auto& origs = _formula->rOrigins();
        auto iter = origs.begin();
        while( iter != origs.end() )
        {
            if( iter->erase( _origin ) == 0 )
            {
                ++iter;
            }
            else
            {
                iter = origs.erase( iter );
            }
        }
        return origs.empty();
    }

    bool ModuleInput::removeOrigins( iterator _formula, const std::vector<FormulasT>& _origins )
    {
        assert( _formula != end() );
        for( auto origsIter = _origins.begin(); origsIter != _origins.end(); ++origsIter )
        {
            if( removeOrigins( _formula, *origsIter ) )
            {
                return true;
            }
        }
        return _formula->origins().empty();
    }

    bool ModuleInput::removeOrigins( iterator _formula, const FormulasT& _origins )
    {
        assert( _formula != end() );
        auto& origs = _formula->rOrigins();
        auto iter = origs.begin();
        while( iter != origs.end() )
        {
            auto formulaAIter = iter->begin();
            auto formulaBIter = _origins.begin();
            while( formulaAIter != iter->end() && formulaBIter != _origins.end() )
            {
                if( iter->value_comp()( *formulaAIter, *formulaBIter ) )
                {
                    ++formulaAIter;
                }
                else if( iter->value_comp()( *formulaBIter, *formulaAIter ) )
                {
                    ++formulaBIter;
                }
                else
                {
                    formulaAIter = iter->erase( formulaAIter );
                    ++formulaBIter;
                }
            }
//                iter->erase( _origins.begin(), _origins.end() ); // TODO: Why does erase not work here?
            if( iter->empty() )
            {
                iter = origs.erase( iter );
            }
            else
            {
                ++iter;
            }
        }
        return origs.empty();
    }
    
    void ModuleInput::updateProperties() const
    {
        mProperties = Condition();
        mProperties |= PROP_IS_PURE_CONJUNCTION | PROP_IS_IN_CNF | PROP_IS_IN_NNF;
        mProperties |= PROP_VARIABLE_DEGREE_LESS_THAN_THREE | PROP_VARIABLE_DEGREE_LESS_THAN_FOUR | PROP_VARIABLE_DEGREE_LESS_THAN_FIVE;
        for( const FormulaWithOrigins& fwo : *this )
        {
            Condition subFormulaConds = fwo.formula().properties();
            if( !(PROP_IS_A_CLAUSE<=subFormulaConds) )
            {
                mProperties &= ~PROP_IS_PURE_CONJUNCTION;
                mProperties &= ~PROP_IS_IN_CNF;
            }
            else if( !(PROP_IS_A_LITERAL<=subFormulaConds) )
                mProperties &= ~PROP_IS_PURE_CONJUNCTION;
            if( !(PROP_IS_IN_NNF<=subFormulaConds) )
                mProperties &= ~PROP_IS_IN_NNF;
            mProperties |= (subFormulaConds & WEAK_CONDITIONS);
        }
    }
    
    pair<ModuleInput::iterator,bool> ModuleInput::add( const FormulaT& _formula, FormulasT&& _origins )
    {
        iterator iter = find( _formula );
        if( iter == end() )
        {
            std::vector<FormulasT> vecOfOrigs;
            vecOfOrigs.emplace_back( move( _origins ) );
            emplace_back( _formula, move( vecOfOrigs ) );
            iterator pos = --end();
            #ifdef MODULE_INPUT_USE_HASHING_FOR_FIND
            mFormulaPositionMap.insert( make_pair( _formula, pos ) );
            #endif
            return make_pair( pos, true );
        }
        else
        {
            iter->rOrigins().emplace_back( move( _origins ) );
            return make_pair( iter, false );
        }
    }

    pair<ModuleInput::iterator,bool> ModuleInput::add( const FormulaT& _formula, std::vector<FormulasT>&& _origins )
    {
        iterator iter = find( _formula );
        if( iter == end() )
        {
            emplace_back( _formula, move( _origins ) );
            iterator pos = --end();
            #ifdef MODULE_INPUT_USE_HASHING_FOR_FIND
            mFormulaPositionMap.insert( make_pair( _formula, pos ) );
            #endif
            return make_pair( pos, true );
        }
        else
        {
            auto& origs = iter->rOrigins();
            origs.reserve( origs.size() + _origins.size() );
            origs.insert( origs.end(), make_move_iterator( _origins.begin() ), make_move_iterator( _origins.end() ) );
            return make_pair( iter, false );
        }
    }
    
    void annotateFormula( const FormulaT&, const vector<parser::Attribute>& )
    {
    }
} // namespace smtrat
