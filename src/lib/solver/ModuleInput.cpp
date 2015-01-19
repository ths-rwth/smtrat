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

    ModuleInput::const_iterator ModuleInput::find( const FormulaT& _formula ) const
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
    
    ModuleInput::iterator ModuleInput::erase( iterator _formula )
    {
        assert( _formula != end() );
        mFormulaPositionMap.erase( _formula->formula() );
        return super::erase( _formula );
    }
    
    bool ModuleInput::removeOrigin( iterator _formula, const FormulaT& _origin )
    {
        assert( _formula != end() );
        if( !_formula->hasOrigins() ) return true;
        auto& origs = *_formula->mOrigins;
        auto iter = origs.begin();
        while( iter != origs.end() )
        {
            if( *iter == _origin || iter->contains( _origin ) )
            {
                iter = origs.erase( iter );
            }
            else
            {
                ++iter;
            }
        }
        if( origs.empty() )
        {
            _formula->mOrigins = nullptr;
            return true;
        }
        return false;
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
    
    pair<ModuleInput::iterator,bool> ModuleInput::add( const FormulaT& _formula, const FormulaT& _origin )
    {
        iterator iter = find( _formula );
        if( iter == end() )
        {
            std::shared_ptr<std::vector<FormulaT>> vecOfOrigs = std::shared_ptr<std::vector<FormulaT>>( new std::vector<FormulaT>() );
            vecOfOrigs->push_back( _origin );
            emplace_back( _formula, std::move( vecOfOrigs ) );
            iterator pos = --end();
            mFormulaPositionMap.insert( make_pair( _formula, pos ) );
            return make_pair( pos, true );
        }
        else
        {
            if( !iter->hasOrigins() )
            {
                iter->mOrigins = std::shared_ptr<std::vector<FormulaT>>( new std::vector<FormulaT>() );
            }
            iter->mOrigins->push_back( _origin );
            return make_pair( iter, false );
        }
    }

    pair<ModuleInput::iterator,bool> ModuleInput::add( const FormulaT& _formula, const std::shared_ptr<std::vector<FormulaT>>& _origins )
    {
        iterator iter = find( _formula );
        if( iter == end() )
        {
            emplace_back( _formula, _origins );
            iterator pos = --end();
            mFormulaPositionMap.insert( make_pair( _formula, pos ) );
            return make_pair( pos, true );
        }
        else
        {
            assert( !iter->hasOrigins() );
//            if( iter->hasOrigins() )
//            {
//                auto& origs = iter->mOrigins;
//                origs.reserve( origs.size() + _origins.size() );
//                origs.insert( origs.end(), make_move_iterator( _origins.begin() ), make_move_iterator( _origins.end() ) );
//            }
//            else
//            {
                iter->mOrigins = _origins;
//            }
            return make_pair( iter, false );
        }
    }
    
    void annotateFormula( const FormulaT&, const vector<parser::Attribute>& )
    {
    }
} // namespace smtrat
