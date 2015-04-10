#pragma once

#include "../Common.h"

namespace smtrat {
namespace parser {
namespace types {

	struct ArithmeticTheory  {
		typedef mpl::vector<Rational> ConstTypes;
		typedef mpl::vector<carl::Variable> VariableTypes;
		typedef mpl::vector<carl::Variable, Rational, Poly> ExpressionTypes;
		typedef mpl::vector<carl::Variable, Rational, Poly> TermTypes;
		typedef carl::mpl_variant_of<TermTypes>::type TermType;
	};
#ifdef PARSER_BITVECTOR
	typedef carl::BVTerm<Poly> BVTerm;
	struct BitvectorTheory {
		typedef mpl::vector<carl::BVVariable, BVTerm> ConstTypes;
		typedef mpl::vector<carl::BVVariable> VariableTypes;
		typedef mpl::vector<carl::BVVariable, BVTerm> ExpressionTypes;
		typedef mpl::vector<carl::BVVariable, BVTerm> TermTypes;
		typedef carl::mpl_variant_of<TermTypes>::type TermType;
	};
#endif
	struct CoreTheory {
		typedef mpl::vector<FormulaT, std::string> ConstTypes;
		typedef mpl::vector<carl::Variable> VariableTypes;
		typedef mpl::vector<FormulaT, std::string> ExpressionTypes;
		typedef mpl::vector<FormulaT, std::string> TermTypes;
		typedef carl::mpl_variant_of<TermTypes>::type TermType;
	};
	struct UninterpretedTheory {
		typedef mpl::vector<carl::UVariable, carl::UFInstance> ConstTypes;
		typedef mpl::vector<carl::UVariable> VariableTypes;
		typedef mpl::vector<carl::UVariable, carl::UFInstance> ExpressionTypes;
		typedef mpl::vector<carl::UVariable, carl::UFInstance> TermTypes;
		typedef carl::mpl_variant_of<TermTypes>::type TermType;
	};

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
	
	struct FunctionInstantiator {
		template<typename T>
		bool convert(const std::vector<TermType>& from, std::vector<T>& to) const {
			VectorVariantConverter<T> converter;
			return converter.convert(from, to);
		}
		virtual bool operator()(const std::vector<TermType>&, TermType&, TheoryError& errors) const {
			errors.next() << "Instantiation of this function is not supported.";
			return false;
		}
	};
	struct UserFunctionInstantiator: public FunctionInstantiator {
	private:
		std::vector<std::pair<std::string, carl::Sort>> arguments;
		carl::Sort sort;
		TermType definition;
	public:
		UserFunctionInstantiator(const std::vector<std::pair<std::string, carl::Sort>>& arguments, const carl::Sort& sort, const TermType& definition):
			arguments(arguments), sort(sort), definition(definition) {}
	};
}
}
}
