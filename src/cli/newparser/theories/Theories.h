#pragma once

#include "../Common.h"
#include "ParserState.h"

#include <carl/util/mpl_utils.h>

#include "Core.h"
#include "Arithmetic.h"

namespace smtrat {
namespace parser {

struct Theories {

	/// Constants
	typedef carl::mpl_concatenate<
			CoreTheory::ConstTypes,
			ArithmeticTheory::ConstTypes
		>::type ConstTypes;
	typedef carl::mpl_variant_of<ConstTypes>::type ConstType;
	
	static void addConstants(qi::symbols<char, ConstType>& constants) {
		CoreTheory::addConstants(constants);
		ArithmeticTheory::addConstants(constants);
	}
	
	typedef carl::mpl_concatenate<
			CoreTheory::ExpressionTypes,
			ArithmeticTheory::ExpressionTypes
		>::type ExpressionTypes;
	typedef carl::mpl_variant_of<ExpressionTypes>::type ExpressionType;
	
	typedef carl::mpl_concatenate<
			CoreTheory::TermTypes,
			ArithmeticTheory::TermTypes
		>::type TermTypes;
	typedef carl::mpl_variant_of<TermTypes>::type TermType;

	static void addSimpleSorts(qi::symbols<char, carl::Sort>& sorts) {
		CoreTheory::addSimpleSorts(sorts);
		ArithmeticTheory::addSimpleSorts(sorts);
	}
	
	Theories(ParserState* state):
		state(state), 
		core(state),
		arithmetic(state)
	{
	}
	
	void addGlobalFormulas(FormulasT& formulas) {
		core.addGlobalFormulas(formulas);
		arithmetic.addGlobalFormulas(formulas);
	}
	void newVariable(const std::string& name, const carl::Sort& sort) {
		if (state->isSymbolFree(name)) {
			if (core.newVariable(name, sort)) return;
			if (arithmetic.newVariable(name, sort)) return;
			SMTRAT_LOG_ERROR("smtrat.parser", "Variable \"" << name << "\" was declared with an invalid sort \"" << sort << "\".");
		} else {
			SMTRAT_LOG_ERROR("smtrat.parser", "Variable \"" << name << "\" will not be declared due to a name clash.");
		}
	}
	
	struct BindVisitor: 
		public boost::static_visitor<>,
		public virtual CoreTheory::BindVisitor, 
		public virtual ArithmeticTheory::BindVisitor 
	{
		using CoreTheory::BindVisitor::operator();
		using ArithmeticTheory::BindVisitor::operator();
		
		BindVisitor(ParserState* state, const std::string& symbol) {
			this->state = state;
			this->symbol = symbol;
		}
		
		void operator()(const std::string& s) {
			SMTRAT_LOG_ERROR("smtrat.parser", "Can not bind string \"" << s << "\".");
		}
	};
	
	void addBinding(const std::string& symbol, const TermType& term) {
		BindVisitor bv(state, symbol);
		boost::apply_visitor(bv, term);
	}

	TermType resolveSymbol(const Identifier& identifier) const {
		if (identifier.indices == nullptr) {
			return state->resolveSymbol<TermType>(identifier.symbol);
		} else {
			SMTRAT_LOG_ERROR("smtrat.parser", "Indexed symbols are not supported yet.");
			return TermType();
		}
	}
	
	TermType functionCall(const Identifier& identifier, const std::vector<TermType>& arguments) {
		TermType result;
		TheoryError te;
		te.setCurrent("Core");
		if (core.functionCall(identifier, arguments, result, te)) return result;
		te.setCurrent("Arithmetic");
		if (arithmetic.functionCall(identifier, arguments, result, te)) return result;
		SMTRAT_LOG_ERROR("smtrat.parser", "Failed to call " << identifier << " with " << arguments << ":" << te);
		std::cout << "Failed!" << std::endl;
		return result;
	}
private:
	ParserState* state;
	CoreTheory core;
	ArithmeticTheory arithmetic;
};
	
}
}
