#pragma once

#include "../Common.h"
#include "config.h"

namespace smtrat {
namespace parser {

struct FixedWidthConstant {
    Integer value;
    std::size_t width;
    FixedWidthConstant(): value(0), width(0) {}
    FixedWidthConstant(const Integer& value, std::size_t width): value(value), width(width) {}
	bool operator<(const FixedWidthConstant& fwc) const {
		return value < fwc.value;
	}
};
inline std::ostream& operator<<(std::ostream& os, const FixedWidthConstant& fwc) {
    return os << fwc.value << "_" << fwc.width;
}

namespace types {
	
	struct CoreTheory {
		typedef mpl::vector<FormulaT, std::string> ConstTypes;
		typedef mpl::vector<carl::Variable> VariableTypes;
		typedef mpl::vector<FormulaT, std::string> ExpressionTypes;
		typedef mpl::vector<FormulaT, std::string> TermTypes;
		typedef carl::mpl_variant_of<TermTypes>::type TermType;
	};
#ifdef PARSER_ENABLE_ARITHMETIC
	struct ArithmeticTheory  {
		typedef mpl::vector<Rational, FixedWidthConstant> ConstTypes;
		typedef mpl::vector<carl::Variable> VariableTypes;
		typedef mpl::vector<carl::Variable, Rational, FixedWidthConstant, Poly> ExpressionTypes;
		typedef mpl::vector<carl::Variable, Rational, FixedWidthConstant, Poly> TermTypes;
		typedef carl::mpl_variant_of<TermTypes>::type TermType;
	};
#endif
#ifdef PARSER_ENABLE_BITVECTOR
	typedef carl::BVTerm BVTerm;
	typedef carl::BVConstraint BVConstraint;
	struct BitvectorTheory {
		typedef mpl::vector<carl::BVVariable, FixedWidthConstant, BVTerm> ConstTypes;
		typedef mpl::vector<carl::BVVariable, BVTerm> VariableTypes;
		typedef mpl::vector<carl::BVVariable, FixedWidthConstant, BVTerm, BVConstraint> ExpressionTypes;
		typedef mpl::vector<carl::BVVariable, FixedWidthConstant, BVTerm, BVConstraint> TermTypes;
		typedef carl::mpl_variant_of<TermTypes>::type TermType;
	};
#endif
#ifdef PARSER_ENABLE_UNINTERPRETED
	struct UninterpretedTheory {
		typedef mpl::vector<carl::UVariable, carl::UFInstance> ConstTypes;
		typedef mpl::vector<carl::UVariable> VariableTypes;
		typedef mpl::vector<carl::UVariable, carl::UFInstance> ExpressionTypes;
		typedef mpl::vector<carl::UVariable, carl::UFInstance> TermTypes;
		typedef carl::mpl_variant_of<TermTypes>::type TermType;
	};
#endif

	typedef carl::mpl_concatenate<
			ArithmeticTheory::ConstTypes,
#ifdef PARSER_BITVECTOR
			BitvectorTheory::ConstTypes,
#endif
			CoreTheory::ConstTypes,
			UninterpretedTheory::ConstTypes
		>::type ConstTypes;
	typedef carl::mpl_variant_of<ConstTypes>::type ConstType;
	
	typedef carl::mpl_concatenate<
			ArithmeticTheory::VariableTypes,
#ifdef PARSER_BITVECTOR
			BitvectorTheory::VariableTypes,
#endif
			CoreTheory::VariableTypes,
			UninterpretedTheory::VariableTypes
		>::type VariableTypes;
	typedef carl::mpl_variant_of<VariableTypes>::type VariableType;
	
	typedef carl::mpl_concatenate<
			ArithmeticTheory::ExpressionTypes,
#ifdef PARSER_BITVECTOR
			BitvectorTheory::ExpressionTypes,
#endif
			CoreTheory::ExpressionTypes,
			UninterpretedTheory::ExpressionTypes
		>::type ExpressionTypes;
	typedef carl::mpl_variant_of<ExpressionTypes>::type ExpressionType;
	
	typedef carl::mpl_concatenate<
			ArithmeticTheory::TermTypes,
#ifdef PARSER_BITVECTOR
			BitvectorTheory::TermTypes,
#endif
			CoreTheory::TermTypes,
			UninterpretedTheory::TermTypes
		>::type TermTypes;
	typedef carl::mpl_variant_of<TermTypes>::type TermType;
	
	typedef carl::mpl_concatenate<
			TermTypes,
			boost::mpl::vector<
				SExpressionSequence<types::ConstType>,
				bool,
				boost::spirit::qi::unused_type
			>
		>::type AttributeTypes;
	typedef carl::mpl_variant_of<AttributeTypes>::type AttributeValue;
	
}
}
}
