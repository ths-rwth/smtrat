#pragma once

#include "Common.h"

#include <carl/util/mpl_utils.h>

#include <boost/mpl/for_each.hpp>
#include <boost/mpl/vector.hpp>
#include <boost/spirit/include/support_unused.hpp>

#define PARSER_ENABLE_ARITHMETIC
#define PARSER_ENABLE_BITVECTOR
#define PARSER_ENABLE_UNINTERPRETED

namespace smtrat {
namespace parser {
	namespace mpl = boost::mpl;

#ifdef PARSER_ENABLE_ARITHMETIC
	#define ARITHMETIC(...) __VA_ARGS__
#else
	#define ARITHMETIC(...)
#endif
#ifdef PARSER_ENABLE_BITVECTOR
	#define BITVECTOR(...) __VA_ARGS__
#else
	#define BITVECTOR(...)
#endif
#ifdef PARSER_ENABLE_UNINTERPRETED
	#define UNINTERPRETED(...) __VA_ARGS__
#else
	#define UNINTERPRETED(...)
#endif

/**
 * Represents a constant of a fixed width.
 */
template<typename T>
struct FixedWidthConstant {
    T value;
    std::size_t width;
    FixedWidthConstant(): value(0), width(0) {}
    FixedWidthConstant(const T& value, std::size_t width): value(value), width(width) {}
	bool operator<(const FixedWidthConstant& fwc) const {
		return value < fwc.value;
	}
};
template<typename T>
inline std::ostream& operator<<(std::ostream& os, const FixedWidthConstant<T>& fwc) {
    return os << fwc.value << "_" << fwc.width;
}

namespace types {
	/**
     * Types of the core theory.
     */
	struct CoreTheory {
		typedef mpl::vector<FormulaT, std::string> ConstTypes;
		typedef mpl::vector<carl::Variable> VariableTypes;
		typedef mpl::vector<FormulaT, std::string> ExpressionTypes;
		typedef mpl::vector<FormulaT, std::string> TermTypes;
		typedef carl::mpl_variant_of<TermTypes>::type TermType;
	};
#ifdef PARSER_ENABLE_ARITHMETIC
    /**
     * Types of the arithmetic theory.
     */
	struct ArithmeticTheory  {
		typedef mpl::vector<Rational, FixedWidthConstant<Integer>> ConstTypes;
		typedef mpl::vector<carl::Variable> VariableTypes;
		typedef mpl::vector<carl::Variable, Rational, FixedWidthConstant<Integer>, Poly> ExpressionTypes;
		typedef mpl::vector<carl::Variable, Rational, FixedWidthConstant<Integer>, Poly> TermTypes;
		typedef carl::mpl_variant_of<TermTypes>::type TermType;
	};
#endif
#ifdef PARSER_ENABLE_BITVECTOR
    /// Typedef for bitvector term.
	typedef carl::BVTerm BVTerm;
	typedef carl::BVVariable BVVariable;
    /// Typedef for bitvector constraint.
	typedef carl::BVConstraint BVConstraint;
    /**
     *  Types of the theory of bitvectors.
     */
	struct BitvectorTheory {
		typedef mpl::vector<BVVariable, FixedWidthConstant<Integer>, BVTerm> ConstTypes;
		typedef mpl::vector<BVVariable> VariableTypes;
		typedef mpl::vector<BVVariable, FixedWidthConstant<Integer>, BVTerm, BVConstraint> ExpressionTypes;
		typedef mpl::vector<BVVariable, FixedWidthConstant<Integer>, BVTerm, BVConstraint> TermTypes;
		typedef carl::mpl_variant_of<TermTypes>::type TermType;
	};
#endif
#ifdef PARSER_ENABLE_UNINTERPRETED
    /**
     * Types of the theory of equalities and uninterpreted functions.
     */
	struct UninterpretedTheory {
		typedef mpl::vector<carl::UVariable, carl::UFInstance> ConstTypes;
		typedef mpl::vector<carl::UVariable> VariableTypes;
		typedef mpl::vector<carl::UVariable, carl::UFInstance> ExpressionTypes;
		typedef mpl::vector<carl::UVariable, carl::UFInstance> TermTypes;
		typedef carl::mpl_variant_of<TermTypes>::type TermType;
	};
#endif

    /**
     * List of all types of constants.
     */
	typedef carl::mpl_concatenate<
			ARITHMETIC(ArithmeticTheory::ConstTypes,)
            BITVECTOR(BitvectorTheory::ConstTypes,)
			CoreTheory::ConstTypes,
			UNINTERPRETED(UninterpretedTheory::ConstTypes)
		>::type ConstTypes;
    /**
     * Variant type for all constants.
     */
	typedef carl::mpl_variant_of<ConstTypes>::type ConstType;
	
    /**
     * List of all types of variables.
     */
	typedef carl::mpl_concatenate<
            ARITHMETIC(ArithmeticTheory::VariableTypes,)
			BITVECTOR(BitvectorTheory::VariableTypes,)
			CoreTheory::VariableTypes,
			UNINTERPRETED(UninterpretedTheory::VariableTypes)
		>::type VariableTypes;
    /**
     * Variant type for all variables.
     */
	typedef carl::mpl_variant_of<VariableTypes>::type VariableType;
	
    /**
     * List of all types of expressions.
     */
	typedef carl::mpl_concatenate<
			ARITHMETIC(ArithmeticTheory::ExpressionTypes,)
			BITVECTOR(BitvectorTheory::ExpressionTypes,)
			CoreTheory::ExpressionTypes,
			UNINTERPRETED(UninterpretedTheory::ExpressionTypes)
		>::type ExpressionTypes;
    /**
     * Variant type for all expressions.
     */
	typedef carl::mpl_variant_of<ExpressionTypes>::type ExpressionType;
	
    /**
     * List of all types of terms.
     */
	typedef carl::mpl_concatenate<
			ARITHMETIC(ArithmeticTheory::TermTypes,)
			BITVECTOR(BitvectorTheory::TermTypes,)
			CoreTheory::TermTypes,
			UNINTERPRETED(UninterpretedTheory::TermTypes)
		>::type TermTypes;
    /**
     * Variant type for all terms.
     */
	typedef carl::mpl_variant_of<TermTypes>::type TermType;
	
    /**
     * List of all types of attributes.
     */
	typedef carl::mpl_concatenate<
			TermTypes,
			boost::mpl::vector<
				SExpressionSequence<types::ConstType>,
				std::string,
				bool,
				boost::spirit::unused_type
			>
		>::type AttributeTypes;
    /**
     * Variant type for all attributes.
     */
	typedef carl::mpl_variant_of<AttributeTypes>::type AttributeValue;
	
}
}
}
