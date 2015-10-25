/**
 * @file Assignment.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2014-01-14
 * @version 2014-10-27

 */

#pragma once

#include "../Common.h"
#include <map>
#include <boost/variant.hpp>
#include <carl/core/RealAlgebraicNumber.h>
#include "vs/SqrtEx.h"
#include "SortValue.h"
#include "UFModel.h"

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

    /**
     * @return true, if the first argument is a variable and the second is a function 
     *                or if both are variables and the first is smaller (lower id)
     *                or if both are function and the first smaller (lower id).
     */
    bool operator<( const ModelVariable& _mvar, const carl::Variable& _var );
    
    /**
     * @return true, if the first argument is a variable and the second is a function 
     *                or if both are variables and the first is smaller (lower id)
     *                or if both are function and the first smaller (lower id).
     */
    bool operator<( const carl::Variable& _var, const ModelVariable& _mvar );

    /**
     * @return true, if the first argument is a bitvector variable that is smaller
     *               than the second argument (by id),
     *               or if the first argument has another type that is ordered
     *               before the bitvector variable type.
     */
    bool operator<( const ModelVariable& _mvar, const carl::BVVariable& _bvvar );

    /**
     * @return true, if the second argument is a bitvector variable and the first argument
     *               is smaller (by id),
     *               or if the second argument has another type and the bitvector
     *               variable type is ordered before the type of the second argument.
     */
    bool operator<( const carl::BVVariable& _bvvar, const ModelVariable& _mvar );

    /**
     * @return true, if the first argument is a variable and the second is a function 
     *                or if both are variables and the first is smaller (lower id)
     *                or if both are function and the first smaller (lower id).
     */
    bool operator<( const ModelVariable& _mvar, const carl::UVariable& _var );
    
    /**
     * @return true, if the first argument is a variable and the second is a function 
     *                or if both are variables and the first is smaller (lower id)
     *                or if both are function and the first smaller (lower id).
     */
    bool operator<( const carl::UVariable& _var, const ModelVariable& _mvar );

    /**
     * @return true, if the first argument is a variable and the second is a function 
     *                or if both are variables and the first is smaller (lower id)
     *                or if both are function and the first smaller (lower id).
     */
    bool operator<( const ModelVariable& _mvar, const carl::UninterpretedFunction& _uf );
    
    /**
     * @return true, if the first argument is a variable and the second is a function 
     *                or if both are variables and the first is smaller (lower id)
     *                or if both are function and the first smaller (lower id).
     */
    bool operator<( const carl::UninterpretedFunction& _uf, const ModelVariable& _mvar );
    
    /**
     * This class represents some value that is assigned to some variable.
     * It is implemented as subclass of a boost::variant.
     * Possible value types are bool, vs::SqrtEx and carl::RealAlgebraicNumberPtr.
     */
    class ModelValue : public boost::variant<bool, vs::SqrtEx, carl::RealAlgebraicNumberPtr<smtrat::Rational>, carl::BVValue, SortValue, UFModel>
    {
        /**
         * Base type we are deriving from.
         */
        typedef boost::variant<bool, vs::SqrtEx, carl::RealAlgebraicNumberPtr<smtrat::Rational>, carl::BVValue, SortValue, UFModel> Super;
        
    public:
        /**
         * Default constructor.
         */
        ModelValue(): Super()
        {}

        /**
         * Initializes the Assignment from some valid type of the underlying variant.
         */
        template<typename T>
        ModelValue(const T& _t): Super(_t)
        {}

        /**
         * Assign some value to the underlying variant.
         * @param t Some value.
         * @return *this.
         */
        template<typename T>
        ModelValue& operator=( const T& _t )
        {
            Super::operator=(_t);
            return *this;
        }

        /**
         * Check if two Assignments are equal.
         * Two Assignments are considered equal, if both are either bool or not bool and their value is the same.
         * 
         * If both Assignments are not bools, the check may return false although they represent the same value.
         * If both are numbers in different representations, this comparison is only done as a "best effort".
         * 
         * @param _ass Another Assignment.
         * @return *this == a.
         */
        bool operator==( const ModelValue& _mval ) const
        {
            if( isBool() && _mval.isBool() )
            {
                return asBool() == _mval.asBool();
            }
            else if( isSqrtEx() && _mval.isSqrtEx() )
            {
                return asSqrtEx() == _mval.asSqrtEx();
            } 
            else if( isRAN() & _mval.isRAN() )
            {
                return std::equal_to<carl::RealAlgebraicNumberPtr<smtrat::Rational>>()(asRAN(), _mval.asRAN());
            }
            else if( isBVValue() && _mval.isBVValue() )
            {
                return asBVValue() == _mval.asBVValue();
            }
            else if( isSortValue() & _mval.isSortValue() )
            {
                return asSortValue() == _mval.asSortValue();
            }
            else if( isUFModel() & _mval.isUFModel() )
            {
                return asUFModel() == _mval.asUFModel();
            }
            return false;
        }

        /**
         * @return true, if the stored value is a bool.
         */
        bool isBool() const
        {
            return type() == typeid(bool);
        }
        
        /**
         * @return true, if the stored value is a square root expression.
         */
        bool isSqrtEx() const
        {
            return type() == typeid(vs::SqrtEx);
        }
        
        /**
         * @return true, if the stored value is a real algebraic number.
         */
        bool isRAN() const
        {
            return type() == typeid(carl::RealAlgebraicNumberPtr<smtrat::Rational>);
        }
        
        /**
         * @return true, if the stored value is a bitvector literal.
         */
        bool isBVValue() const
        {
            return type() == typeid(carl::BVValue);
        }

        /**
         * @return true, if the stored value is a sort value.
         */
        bool isSortValue() const
        {
            return type() == typeid(SortValue);
        }
        
        /**
         * @return true, if the stored value is a uninterpreted function model.
         */
        bool isUFModel() const {
            return type() == typeid(UFModel);
        }

        /**
         * @return The stored value as a bool.
         */
        bool asBool() const
        {
            assert( isBool() );
            return boost::get<bool>(*this);
        }
        
        /**
         * @return The stored value as a square root expression.
         */
        const vs::SqrtEx& asSqrtEx() const
        {
            assert( isSqrtEx() );
            return boost::get<vs::SqrtEx>(*this);
        }
        
        /**
         * @return The stored value as a real algebraic number.
         */
        carl::RealAlgebraicNumberPtr<smtrat::Rational> asRAN() const
        {
            assert( isRAN() );
            return boost::get<carl::RealAlgebraicNumberPtr<smtrat::Rational>>(*this);
        }
        
        /**
         * @return The stored value as a real algebraic number.
         */
        const carl::BVValue& asBVValue() const
        {
            assert( isBVValue() );
            return boost::get<carl::BVValue>(*this);
        }

        /**
         * @return The stored value as a sort value.
         */
        const SortValue& asSortValue() const
        {
            assert( isSortValue() );
            return boost::get<SortValue>(*this);
        }
        
        /**
         * @return The stored value as a uninterpreted function model.
         */
        const UFModel& asUFModel() const
        {
            assert( isUFModel() );
            return boost::get<UFModel>(*this);
        }
    };
    
    /// Data type for a assignment assigning a variable, represented as a string, a real algebraic number, represented as a string.
    class Model : public std::map<ModelVariable,ModelValue> {};
    
    /**
     * Obtains all assignments which can be transformed to rationals and stores them in the passed map.
     * @param _model The model from which to obtain the rational assignments.
     * @param _rationalAssigns The map to store the rational assignments in.
     * @return true, if the entire model could be transformed to rational assignments. (not possible if, e.g., sqrt is contained)
     */
    bool getRationalAssignmentsFromModel( const Model& _model, EvalRationalMap& _rationalAssigns );
            
    /**
     * @param _assignment The assignment for which to check whether the given formula is satisfied by it.
     * @param _formula The formula to be satisfied.
     * @return 0, if this formula is violated by the given assignment;
     *         1, if this formula is satisfied by the given assignment;
     *         2, otherwise.
     */
    unsigned satisfies( const Model& _assignment, const FormulaT& _formula );
    
    bool isPartOf( const EvalRationalMap& _assignment, const Model& _model );
    
    /**
     * @param _model The assignment for which to check whether the given formula is satisfied by it.
     * @param _assignment The map to store the rational assignments in.
     * @param _formula The formula to be satisfied.
     * @return 0, if this formula is violated by the given assignment;
     *         1, if this formula is satisfied by the given assignment;
     *         2, otherwise.
     */
    unsigned satisfies( const Model& _model, const EvalRationalMap& _assignment, const std::map<carl::BVVariable, carl::BVTerm>& bvAssigns, const FormulaT& _formula );
    
    void getDefaultModel( Model& _defaultModel, const carl::UEquality& _constraint, bool _overwrite = true, size_t _seed = 0 );
    void getDefaultModel( Model& _defaultModel, const carl::BVTerm& _constraint, bool _overwrite = true, size_t _seed = 0 );
    void getDefaultModel( Model& _defaultModel, const ConstraintT& _constraint, bool _overwrite = true, size_t _seed = 0 );
    void getDefaultModel( Model& _defaultModel, const FormulaT& _formula, bool _overwrite = true, size_t _seed = 0 );
    
    std::ostream& operator<<( std::ostream& _out, const Model& _model );
}