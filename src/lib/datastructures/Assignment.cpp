/**
 * Class to create a state object.
 * @author Florian Corzilius
 * @since 2014-01-14
 * @version 2014-01-14
 */

#include "Assignment.h"
#include "SortValueManager.h"

namespace smtrat
{
    bool operator<( const ModelVariable& _mvar, const carl::Variable& _var )
    {
        if( _mvar.isVariable() )
            return _mvar.asVariable() < _var;
        return false;
    }
    
    bool operator<( const carl::Variable& _var, const ModelVariable& _mvar )
    {
        if( _mvar.isVariable() )
            return _var < _mvar.asVariable();
        return true;
    }
    
	bool operator<(const ModelVariable& _mvar, const carl::BVVariable& _bvvar)
    {
        if( _mvar.isBVVariable() )
            return _mvar.asBVVariable() < _bvvar;
        return _mvar.isVariable();
    }

    bool operator<( const carl::BVVariable& _bvvar, const ModelVariable& _mvar )
    {
        if( _mvar.isBVVariable() )
            return _bvvar < _mvar.asBVVariable();
        return !_mvar.isVariable();
    }

    bool operator<( const ModelVariable& _mvar, const carl::UVariable& _uv )
    {
        if( _mvar.isUVariable() )
            return _mvar.asUVariable() < _uv;
        return !_mvar.isFunction();
    }
    
    bool operator<( const carl::UVariable& _uv, const ModelVariable& _mvar )
    {
        if( _mvar.isUVariable() )
            return _uv < _mvar.asUVariable();
        return _mvar.isFunction();
    }
    
    bool operator<( const ModelVariable& _mvar, const carl::UninterpretedFunction& _uf )
    {
        if( _mvar.isFunction() )
            return _mvar.asFunction() < _uf;
        return true;
    }
    
    bool operator<( const carl::UninterpretedFunction& _uf, const ModelVariable& _mvar )
    {
        if( _mvar.isFunction() )
            return _uf < _mvar.asFunction();
        return false;
    }
    
    bool getRationalAssignmentsFromModel( const Model& _model, EvalRationalMap& _rationalAssigns )
    {
        bool result = true;
        for( auto ass = _model.begin(); ass != _model.end(); ++ass )
        {   
            if (ass->second.isBool())
            {
                assert( ass->first.isVariable() );
                _rationalAssigns.insert( _rationalAssigns.end(), std::make_pair( ass->first.asVariable(), (ass->second.asBool() ? ONE_RATIONAL : ZERO_RATIONAL) ) );
            }
            else if (ass->second.isSqrtEx())
            {
                if( ass->second.asSqrtEx().isConstant() && !ass->second.asSqrtEx().hasSqrt() )
                {
                    assert( ass->first.isVariable() );
                    Rational value = ass->second.asSqrtEx().constantPart().constantPart()/ass->second.asSqrtEx().denominator().constantPart();
                    assert( !(ass->first.asVariable().getType() == carl::VariableType::VT_INT) || carl::isInteger( value ) );
                    _rationalAssigns.insert( _rationalAssigns.end(), std::make_pair(ass->first.asVariable(), value));
                }
                else
                {
                    result = false;
                }
            }
            else if (ass->second.isRAN())
            {
                if (ass->second.asRAN()->isNumeric())
                {
                    assert( ass->first.isVariable() );
                    _rationalAssigns.insert( _rationalAssigns.end(), std::make_pair(ass->first.asVariable(), ass->second.asRAN()->value()) );
                }
            }
            else if (ass->second.isSortValue())
            {
                assert( ass->first.isVariable() );
                _rationalAssigns.insert( _rationalAssigns.end(), std::make_pair(ass->first.asVariable(), ass->second.asSortValue().id()) );
            }
        }
        return result;
    }
    
    unsigned satisfies( const Model& _assignment, const FormulaT& _formula )
    {
        EvalRationalMap rationalAssigns;
        getRationalAssignmentsFromModel( _assignment, rationalAssigns );
        return satisfies( _assignment, rationalAssigns, _formula );
    }
    
    bool isPartOf( const EvalRationalMap& _assignment, const Model& _model )
    {
        auto assIter = _assignment.begin();
        auto modIter = _model.begin();
        while( assIter != _assignment.end() && modIter != _model.end() )
        {
            if( modIter->first < assIter->first )
            {
                ++assIter; 
            }
            else if( assIter->first < modIter->first )
            {
                return false;
            }
            else
            {
                ++assIter;
                ++modIter;  
            }
        }
        return assIter == _assignment.end();
    }
    
    unsigned satisfies( const Model& _model, const EvalRationalMap& _assignment, const FormulaT& _formula )
    {
        assert( isPartOf( _assignment, _model ) );
        switch( _formula.getType() )
        {
            case carl::FormulaType::TRUE:
            {
                return 1;
            }
            case carl::FormulaType::FALSE:
            {
                return 0;
            }
            case carl::FormulaType::BOOL:
            {
                auto ass = _assignment.find( _formula.boolean() );
                return ass == _assignment.end() ? 2 : (ass->second == ONE_RATIONAL ? 1 : 0);
            }
            case carl::FormulaType::CONSTRAINT:
            {
                return _formula.constraint().satisfiedBy( _assignment );
            }
			case carl::FormulaType::BITVECTOR:
            {
                ///@todo do something here
                return 2;
            }
            case carl::FormulaType::NOT:
            {
                switch( satisfies( _model, _assignment, _formula.subformula() ) )
                {
                    case 0:
                        return 1;
                    case 1:
                        return 0;
                    default:
                        return 2;
                }   
            }
            case carl::FormulaType::OR:
            {
                unsigned result = 0;
                for( const FormulaT& subFormula : _formula.subformulas() )
                {
                    switch( satisfies( _model, _assignment, subFormula ) )
                    {
                        case 0:
                            break;
                        case 1:
                            return 1;
                        default:
                            if( result != 2 ) result = 2;
                    }
                }
                return result;
            }
            case carl::FormulaType::AND:
            {
                unsigned result = 1;
                for( const FormulaT& subFormula : _formula.subformulas() )
                {
                    switch( satisfies( _model, _assignment, subFormula ) )
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
            case carl::FormulaType::IMPLIES:
            {
                unsigned result = satisfies( _model, _assignment, _formula.premise() );
                if( result == 0 ) return 1;
                switch( satisfies( _model, _assignment, _formula.conclusion() ) )
                {
                    case 0:
                        return result == 1 ? 0 : 2;
                    case 1:
                        return 1;
                    default:
                        return 2;
                }
            }
            case carl::FormulaType::ITE:
            {
                unsigned result = satisfies( _model, _assignment, _formula.condition() );
                switch( result )
                {
                    case 0:
                        return satisfies( _model, _assignment, _formula.secondCase() );
                    case 1:
                        return satisfies( _model, _assignment, _formula.firstCase() );
                    default:
                        return 2;
                }
            }
            case carl::FormulaType::IFF:
            {
                auto subFormula = _formula.subformulas().begin();
                unsigned result = satisfies( _model, _assignment, *subFormula );
                bool containsTrue = (result == 1 ? true : false);
                bool containsFalse = (result == 0 ? true : false);
                ++subFormula;
                while( subFormula != _formula.subformulas().end() )
                {
                    unsigned resultTmp = satisfies( _model, _assignment, *subFormula );
                    switch( resultTmp )
                    {
                        case 0:
                            containsFalse = true;
                            break;
                        case 1:
                            containsTrue = true;
                        default:
                            result = 2;
                    }
                    if( containsFalse && containsTrue )
                        return 0;
                    ++subFormula;
                }
                return (result == 2 ? 2 : 1);
            }
            case carl::FormulaType::XOR:
            {
                auto subFormula = _formula.subformulas().begin();
                unsigned result = satisfies( _model, _assignment, *subFormula );
                if( result == 2 ) return 2;
                ++subFormula;
                while( subFormula != _formula.subformulas().end() )
                {
                    unsigned resultTmp = satisfies( _model, _assignment, *subFormula );
                    if( resultTmp == 2 ) return 2;
                    result = resultTmp != result;
                    ++subFormula;
                }
                return result;
            }
            case carl::FormulaType::EXISTS:
            {
                ///@todo do something here
                return 2;
            }
            case carl::FormulaType::FORALL:
            {
                ///@todo do something here
                return 2;
            }
            case carl::FormulaType::UEQ:
            {
                const carl::UEquality& eq = _formula.uequality();
                SortValue::IDType lhsResult = 0;
                SortValue::IDType rhsResult = 0;
                // get sortvalue for lhs and rhs
                if( eq.lhsIsUV() )
                {
                    auto iter = _model.find( eq.lhsAsUV() );
                    if( iter == _model.end() )
                        return 2;
                    assert( iter->second.isSortValue() );
                    lhsResult = iter->second.asSortValue().id();
                }
                else
                {
                    auto iter = _model.find( eq.lhsAsUF().uninterpretedFunction() );
                    if( iter == _model.end() )
                        return 2;
                    assert( iter->second.isUFModel() );
                    const UFModel& ufm = iter->second.asUFModel();
                    std::vector<SortValue> inst;
                    for( const carl::UVariable& arg : eq.lhsAsUF().args() )
                    {
                        auto iterB = _model.find( arg() );
                        if( iterB == _model.end() )
                            return 2;
                        assert( iterB->second.isSortValue() );
                        inst.push_back( iterB->second.asSortValue() );
                    }
                    SortValue sv = ufm.get( inst );
                    if( sv == defaultSortValue( sv.sort() ) )
                        return 2;
                    lhsResult = sv.id();
                }
                if( eq.rhsIsUV() )
                {
                    auto iter = _model.find( eq.rhsAsUV() );
                    if( iter == _model.end() )
                        return 2;
                    assert( iter->second.isSortValue() );
                    rhsResult = iter->second.asSortValue().id();
                }
                else
                {
                    auto iter = _model.find( eq.rhsAsUF().uninterpretedFunction() );
                    if( iter == _model.end() )
                        return 2;
                    assert( iter->second.isUFModel() );
                    const UFModel& ufm = iter->second.asUFModel();
                    std::vector<SortValue> inst;
                    for( const carl::UVariable& arg : eq.rhsAsUF().args() )
                    {
                        auto iterB = _model.find( arg() );
                        if( iterB == _model.end() )
                            return 2;
                        assert( iterB->second.isSortValue() );
                        inst.push_back( iterB->second.asSortValue() );
                    }
                    SortValue sv = ufm.get( inst );
                    if( sv == defaultSortValue( sv.sort() ) )
                        return 2;
                    rhsResult = sv.id();
                }
                // check eq.negated() <=> sv(lhs) != sv(rhs)
                return eq.negated() ? lhsResult != rhsResult : lhsResult == rhsResult;
            }
            default:
            {
                assert( false );
                std::cerr << "Undefined operator!" << std::endl;
                return 2;
            }
        }
    }
    
    std::ostream& operator<<( std::ostream& _out, const Model& _model )
    {
        _out << "(";
        for( Model::const_iterator ass = _model.begin(); ass != _model.end(); ++ass )
        {
            if (ass != _model.begin()) _out << " ";
			if (ass->first.isVariable() || ass->first.isBVVariable())
                _out << "(" << ass->first << " " << ass->second << ")" << endl;
            else if( ass->first.isUVariable() )
                _out << "(define-fun " << ass->first << " () " << ass->first.asUVariable().domain() << " " << ass->second << ")" << endl;
            else
            {
                assert( ass->first.isFunction() );
                _out << ass->second.asUFModel() << endl;
            }
        }
        _out << ")" << endl;
        return _out;
    }
}    
