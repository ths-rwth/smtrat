#pragma once

#include "Expression.h"
#include "ExpressionPool.h"
#include "ExpressionVisitor.h"
#include "ExpressionConverter.h"

namespace smtrat {
	
	void visiting(const Expression& expr) {
		std::cout << expr << std::endl;
	}
	
	void testExpression() {
		carl::Variable x = carl::fresh_boolean_variable("x");
		expression::Expression e(x);
		
		expression::Expression e2(expression::NaryType::AND, { e, e });
		expression::Expression e3(expression::NaryType::AND, { e, e, e2 });
		expression::Expression e4(expression::UnaryType::NOT, e3);
		expression::Expression e5(expression::UnaryType::NOT, e4);
		
		std::cout << e3 << std::endl;
		std::cout << e4 << std::endl;
		std::cout << e5 << std::endl;
		
		expression::ExpressionConverter c;
		
		FormulaT f = c(e3);
		
		std::cout << f << std::endl;
	}
	
} 
