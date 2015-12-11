#pragma once

#include <boost/variant.hpp>

#include "../../Common.h"

namespace smtrat
{

	class ModelVariable : public boost::variant<carl::Variable,carl::BVVariable,carl::UVariable,carl::UninterpretedFunction>
    {
        /**
         * Base type we are deriving from.
         */
        typedef boost::variant<carl::Variable,carl::BVVariable,carl::UVariable,carl::UninterpretedFunction> Super;
        
    public:
        /**
         * Default constructor.
         */
        ModelVariable(): Super()
        {}

        /**
         * Initializes the ModelVariable from some valid type of the underlying variant.
         */
        template<typename T>
        ModelVariable(const T& _t): Super(_t)
        {}

        /**
         * Assign some value to the underlying variant.
         * @param t Some value.
         * @return *this.
         */
        template<typename T>
        ModelVariable& operator=( const T& _t )
        {
            Super::operator=(_t);
            return *this;
        }
        
        /**
         * @return true, if the stored value is a variable.
         */
        bool isVariable() const
        {
            return type() == typeid(carl::Variable);
        }
        
        /**
         * @return true, if the stored value is a bitvector variable.
         */
        bool isBVVariable() const
        {
            return type() == typeid(carl::BVVariable);
        }

        /**
         * @return true, if the stored value is an uninterpreted variable.
         */
        bool isUVariable() const
        {
            return type() == typeid(carl::UVariable);
        }

        /**
         * @return true, if the stored value is a function.
         */
        bool isFunction() const
        {
            return type() == typeid(carl::UninterpretedFunction);
        }
        
        /**
         * @return The stored value as a variable.
         */
        carl::Variable::Arg asVariable() const
        {
            assert( isVariable() );
            return boost::get<carl::Variable>(*this);
        }
        
        /**
         * @return The stored value as a bitvector variable.
         */
        const carl::BVVariable& asBVVariable() const
        {
            assert( isBVVariable() );
            return boost::get<carl::BVVariable>(*this);
        }

        /**
         * @return The stored value as an uninterpreted variable.
         */
        const carl::UVariable& asUVariable() const
        {
            assert( isUVariable() );
            return boost::get<carl::UVariable>(*this);
        }
        
        /**
         * @return The stored value as a function.
         */
        const carl::UninterpretedFunction& asFunction() const
        {
            assert( isFunction() );
            return boost::get<carl::UninterpretedFunction>(*this);
        }

        /**
         * @return true, if the first argument is a variable and the second is a function 
         *                or if both are variables and the first is smaller (lower id)
         *                or if both are function and the first smaller (lower id).
         */
        bool operator<( const ModelVariable& _mvar ) const
        {
            if( isVariable() )
            {
                if( _mvar.isVariable() ) return asVariable() < _mvar.asVariable();
                assert( _mvar.isBVVariable() || _mvar.isUVariable() || _mvar.isFunction() );
                return true;
            }
            if( isBVVariable() )
            {
                if( _mvar.isVariable() ) return false;
                if( _mvar.isBVVariable() ) return asBVVariable() < _mvar.asBVVariable();
                assert( _mvar.isUVariable() || _mvar.isFunction() );
                return true;
            }
            if( isUVariable() )
            {
				if( _mvar.isVariable() || _mvar.isBVVariable() ) return false;
                if( _mvar.isUVariable() ) return asUVariable() < _mvar.asUVariable();
                assert( _mvar.isFunction() );
                return true;
            }
            if( isFunction() )
            {
                if( _mvar.isVariable() || _mvar.isBVVariable() || _mvar.isUVariable() ) return false;
                if( _mvar.isFunction() ) return asFunction() < _mvar.asFunction();
            }
            assert( false );
            return false;
        }
        
        /**
         * @return true, if the first and the second are either both variables or both functions 
         *               and in the first case the variables are equal (equal ids)
         *                or in the second case the functions are equal (equal ids).
         */
        bool operator==( const ModelVariable& _mvar ) const
        {
            if( isVariable() )
            {
                if( _mvar.isVariable() ) return asVariable() == _mvar.asVariable();
                return false;
            }
            if( isBVVariable() )
            {
                if( _mvar.isBVVariable() ) return asBVVariable() == _mvar.asBVVariable();
                return false;
            }
            if( isUVariable() )
            {
                if( _mvar.isUVariable() ) return asUVariable() == _mvar.asUVariable();
                return false;
            }
            assert( isFunction() );
            if( _mvar.isFunction() )
                return asFunction() == _mvar.asFunction();
            return false;
        }
    };
	
	
	inline bool operator<( const ModelVariable& _mvar, const carl::Variable& _var )
	{
	    if( _mvar.isVariable() )
	        return _mvar.asVariable() < _var;
	    return false;
	}

	inline bool operator<( const carl::Variable& _var, const ModelVariable& _mvar )
	{
	    if( _mvar.isVariable() )
	        return _var < _mvar.asVariable();
	    return true;
	}

	inline bool operator<(const ModelVariable& _mvar, const carl::BVVariable& _bvvar)
	{
	    if( _mvar.isBVVariable() )
	        return _mvar.asBVVariable() < _bvvar;
	    return _mvar.isVariable();
	}

	inline bool operator<( const carl::BVVariable& _bvvar, const ModelVariable& _mvar )
	{
	    if( _mvar.isBVVariable() )
	        return _bvvar < _mvar.asBVVariable();
	    return !_mvar.isVariable();
	}

	inline bool operator<( const ModelVariable& _mvar, const carl::UVariable& _uv )
	{
	    if( _mvar.isUVariable() )
	        return _mvar.asUVariable() < _uv;
	    return !_mvar.isFunction();
	}

	inline bool operator<( const carl::UVariable& _uv, const ModelVariable& _mvar )
	{
	    if( _mvar.isUVariable() )
	        return _uv < _mvar.asUVariable();
	    return _mvar.isFunction();
	}

	inline bool operator<( const ModelVariable& _mvar, const carl::UninterpretedFunction& _uf )
	{
	    if( _mvar.isFunction() )
	        return _mvar.asFunction() < _uf;
	    return true;
	}

	inline bool operator<( const carl::UninterpretedFunction& _uf, const ModelVariable& _mvar )
	{
	    if( _mvar.isFunction() )
	        return _uf < _mvar.asFunction();
	    return false;
	}
}
