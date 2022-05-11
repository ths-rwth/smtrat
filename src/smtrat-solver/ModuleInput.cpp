/**
 * @file ModuleInput.cpp
 *
 * @author   Florian Corzilius
 * @version: 2014-05-16
 */

#include "ModuleInput.h"

#include <carl-formula/model/Assignment.h>

// Main smtrat namespace.
namespace smtrat
{   
    unsigned ModuleInput::satisfiedBy( const EvalRationalMap& _assignment ) const
    {
        unsigned result = 1;
        for( const FormulaWithOrigins& fwo : *this )
        {
            switch( carl::model::satisfiedBy(fwo.formula(), Model(_assignment)) )
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
        unsigned result = 1;
        for( const FormulaWithOrigins& fwo : *this )
        {
			auto res = carl::model::substitute(fwo.formula(), _assignment);
			SMTRAT_LOG_DEBUG("smtrat.module", "Checking whether model satisfies " << fwo.formula() << " -> " << res);
			if (res.is_false()) return 0;
			if (!res.is_true()) result = 2;
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
            if( *iter == _origin || (iter->type() == carl::FormulaType::AND && iter->contains( _origin )) )
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
        mProperties = carl::Condition();
        mProperties |= carl::PROP_IS_PURE_CONJUNCTION | carl::PROP_IS_LITERAL_CONJUNCTION | carl::PROP_IS_IN_CNF | carl::PROP_IS_IN_NNF;
        for( const FormulaWithOrigins& fwo : *this )
        {
            carl::Condition subFormulaConds = fwo.formula().properties();
            if( !(carl::PROP_IS_A_CLAUSE<=subFormulaConds) )
            {
                mProperties &= ~carl::PROP_IS_PURE_CONJUNCTION;
                mProperties &= ~carl::PROP_IS_LITERAL_CONJUNCTION;
                mProperties &= ~carl::PROP_IS_IN_CNF;
            }
            else if( !(carl::PROP_IS_AN_ATOM<=subFormulaConds) )
                mProperties &= ~carl::PROP_IS_PURE_CONJUNCTION;
            if( !(carl::PROP_IS_IN_NNF<=subFormulaConds) )
                mProperties &= ~carl::PROP_IS_IN_NNF;
            mProperties |= (subFormulaConds & carl::WEAK_CONDITIONS);
        }
        mPropertiesUpdated = true;
    }

    std::pair<ModuleInput::iterator,bool> ModuleInput::add( const FormulaT& _formula, bool _hasSingleOrigin, const FormulaT& _origin, const std::shared_ptr<std::vector<FormulaT>>& _origins, bool _mightBeConjunction )
    {
        if( _mightBeConjunction && _formula.type() == carl::FormulaType::AND )
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
    void annotateFormula( const FormulaT&, const std::vector<AnnotationType>& )
    {
    }
} // namespace smtrat
