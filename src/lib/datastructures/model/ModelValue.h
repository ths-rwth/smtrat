#pragma once

#include <memory>
#include <boost/variant.hpp>

#include "../../Common.h"
#include <carl/core/RealAlgebraicNumber.h>
#include "../SortValue.h"
#include "../UFModel.h"
#include "../vs/SqrtEx.h"

namespace smtrat
{
	class ModelSubstitution;
	using ModelSubstitutionPtr = std::shared_ptr<ModelSubstitution>;

	/**
	 * This class represents infinity or minus infinity, depending on its flag positive.
	 * The default is minus infinity.
	 */
	struct InfinityValue {
		bool positive = false;
		explicit InfinityValue() {}
		explicit InfinityValue(bool positive): positive(positive) {}
	};
    
	inline std::string toString(const InfinityValue& iv, bool _infix) {
        if( _infix )
        {
            std::string result = iv.positive ? "+" : "-";
            result += "infinity";
            return result;
        }
        if( iv.positive )
            return "infinity";
        return "(- infinity)";
	}
    
	inline std::ostream& operator<<(std::ostream& os, const InfinityValue& iv) {
		return os << (iv.positive ? "+" : "-") << "infinity";
	}
	
    /**
     * This class represents some value that is assigned to some variable.
     * It is implemented as subclass of a boost::variant.
     * Possible value types are bool, vs::SqrtEx and carl::RealAlgebraicNumberPtr.
     */
    class ModelValue : public boost::variant<bool, Rational, Poly, vs::SqrtEx, carl::RealAlgebraicNumber<smtrat::Rational>, carl::BVValue, SortValue, UFModel, InfinityValue, ModelSubstitutionPtr>
    {
        /**
         * Base type we are deriving from.
         */
        using Super = boost::variant<bool, Rational, Poly, vs::SqrtEx, carl::RealAlgebraicNumber<smtrat::Rational>, carl::BVValue, SortValue, UFModel, InfinityValue, ModelSubstitutionPtr>;
        
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
//        template<>
//        ModelValue(const vs::SqrtEx& _se)
//        {
//            Super(_se);
//        }

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
            else if( isRational() && _mval.isRational() )
            {
                return asRational() == _mval.asRational();
            }
			else if( isPoly() && _mval.isPoly() )
			{
				return asPoly() == _mval.asPoly();
			}
            else if( isSqrtEx() && _mval.isSqrtEx() )
            {
                return asSqrtEx() == _mval.asSqrtEx();
            } 
            else if( isRAN() & _mval.isRAN() )
            {
                return std::equal_to<carl::RealAlgebraicNumber<smtrat::Rational>>()(asRAN(), _mval.asRAN());
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
         * @return true, if the stored value is a rational.
         */
        bool isRational() const
        {
            return type() == typeid(Rational);
        }
		
		bool isPoly() const {
			return type() == typeid(Poly);
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
            return type() == typeid(carl::RealAlgebraicNumber<smtrat::Rational>);
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
         * @return true, if the stored value is +infinity.
         */
        bool isPlusInfinity() const {
            return (type() == typeid(InfinityValue)) && boost::get<InfinityValue>(*this).positive;
        }
		/**
         * @return true, if the stored value is -infinity.
         */
        bool isMinusInfinity() const {
            return (type() == typeid(InfinityValue)) && !boost::get<InfinityValue>(*this).positive;
        }
		
		bool isSubstitution() const {
			return (type() == typeid(ModelSubstitutionPtr));
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
         * @return The stored value as a rational.
         */
        const Rational& asRational() const
        {
            assert( isRational() );
            return boost::get<Rational>(*this);
        }
		
		const Poly& asPoly() const
		{
			assert( isPoly() );
			return boost::get<Poly>(*this);
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
        carl::RealAlgebraicNumber<smtrat::Rational> asRAN() const
        {
            assert( isRAN() );
            return boost::get<carl::RealAlgebraicNumber<smtrat::Rational>>(*this);
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
		/**
         * @return The stored value as a infinity value.
         */
        const InfinityValue& asInfinity() const
        {
            assert( isPlusInfinity() || isMinusInfinity() );
            return boost::get<InfinityValue>(*this);
        }
		
		const ModelSubstitutionPtr& asSubstitution() const {
			assert(isSubstitution());
			return boost::get<ModelSubstitutionPtr>(*this);
		}
		ModelSubstitutionPtr& asSubstitution() {
			assert(isSubstitution());
			return boost::get<ModelSubstitutionPtr>(*this);
		}
        
    };
}
