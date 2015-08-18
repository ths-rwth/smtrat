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
            std::cout << fwo.formula() << " -> ";
            switch( fwo.formula().satisfiedBy( _assignment ) )
            {
                case 0:
                    std::cout << "0" << std::endl;
                    return 0;
                case 1:
                    std::cout << "1" << std::endl;
                    break;
                default:
                    std::cout << "2" << std::endl;
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
//        std::cout << "Assignment:" << std::endl;
//        for( const auto& a : _assignment )
//            std::cout << a.first << " -> " << a.second << std::endl;
//        std::cout << "Rational assignment:" << std::endl;
//        for( const auto& ra : rationalAssigns )
//            std::cout << ra.first << " -> " << ra.second << std::endl;
        for( const FormulaWithOrigins& fwo : *this )
        {
//            std::cout << fwo.formula() << " satisfied = ";
            switch( satisfies( _assignment, rationalAssigns, fwo.formula() ) )
            {
                case 0:
                {
//                    std::cout << "0" << std::endl;
                    return 0;
                }
                case 1:
                {
//                    std::cout << "1" << std::endl;
                    break;
                }
                default:
                {
//                    std::cout << "2" << std::endl;
                    if( result != 2 ) result = 2;
                }
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
        mPropertiesUpdated = false;
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
            if( *iter == _origin || (iter->getType() == carl::FormulaType::AND && iter->contains( _origin )) )
            {
                if (iter != --origs.end())
                {
                    *iter = origs.back();
                    origs.pop_back();
                }
                else
                {
                    origs.pop_back();
                    break;
                }
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
    
    bool ModuleInput::removeOrigins( iterator _formula, const std::shared_ptr<std::vector<FormulaT>>& _origins )
    {
        assert( _formula != end() );
        if( !_formula->hasOrigins() ) return true;
        if( _formula->mOrigins == _origins )
        {
            _formula->mOrigins = nullptr;
            return true;
        }
        auto& origs = *_formula->mOrigins;
        for( auto& orig : *_origins )
        {
            auto iter = std::find( origs.begin(), origs.end(), orig );
            if( iter != origs.end() )
            {
                *iter = origs.back();
                origs.pop_back();
            }
        }
        if( origs.empty() )
        {
            _formula->mOrigins = nullptr;
            return true;
        }
        return false;
    }
    
    void ModuleInput::updateProperties()
    {
        mProperties = Condition();
        mProperties |= PROP_IS_PURE_CONJUNCTION | PROP_IS_IN_CNF | PROP_IS_IN_NNF;
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
        mPropertiesUpdated = true;
    }

    pair<ModuleInput::iterator,bool> ModuleInput::add( const FormulaT& _formula, bool _hasSingleOrigin, const FormulaT& _origin, const std::shared_ptr<std::vector<FormulaT>>& _origins, bool _mightBeConjunction )
    {
        if( _mightBeConjunction && _formula.getType() == carl::FormulaType::AND )
        {
            std::pair<iterator,bool> res = std::pair<iterator,bool>(end(), false);
            auto formulaIter = _formula.subformulas().begin();
            while( !res.second && formulaIter != _formula.subformulas().end() )
            {
                res = add( *formulaIter, _hasSingleOrigin, _origin, _origins );
                ++formulaIter;
            }
            while( formulaIter != _formula.subformulas().end() )
            {
                add( *formulaIter, _hasSingleOrigin, _origin, _origins );
                ++formulaIter;
            }
            return res;
        }
        else
        {
            iterator iter = find( _formula );
            if( iter == end() )
            {
                mPropertiesUpdated = false;
                if( _hasSingleOrigin )
                {
                    std::shared_ptr<std::vector<FormulaT>> vecOfOrigs = std::shared_ptr<std::vector<FormulaT>>( new std::vector<FormulaT>() );
                    vecOfOrigs->push_back( _origin );
                    emplace_back( _formula, std::move( vecOfOrigs ) );
                }
                else
                {
                    emplace_back( _formula, _origins );
                }
                iterator pos = --end();
                mFormulaPositionMap.insert( make_pair( _formula, pos ) );
                return make_pair( pos, true );
            }
            else
            {
                if( _hasSingleOrigin )
                {
                    if( !iter->hasOrigins() )
                    {
                        iter->mOrigins = std::shared_ptr<std::vector<FormulaT>>( new std::vector<FormulaT>() );
                    }
                    iter->mOrigins->push_back( _origin );
                    return make_pair( iter, false );
                }
                if( _origins != nullptr )
                {
                    if( iter->hasOrigins() )
                    {
                        iter->mOrigins = std::shared_ptr<std::vector<FormulaT>>( new std::vector<FormulaT>( *iter->mOrigins ) );
                        iter->mOrigins->insert( iter->mOrigins->end(), _origins->begin(), _origins->end() );
                    }
                    else
                    {
                        iter->mOrigins = _origins;
                    }
                }
                return make_pair( iter, false );
            }
        }
    }
    
    template<typename AnnotationType>
    void annotateFormula( const FormulaT&, const vector<AnnotationType>& )
    {
    }
} // namespace smtrat
