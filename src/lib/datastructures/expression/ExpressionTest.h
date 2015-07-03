#pragma once

#include "Expression.h"
#include "ExpressionPool.h"
#include "ExpressionVisitor.h"

namespace smtrat {
	
	void visiting(const Expression& expr) {
		std::cout << expr << std::endl;
	}
	
	void testExpression() {
		carl::Variable x = carl::freshBooleanVariable("x");
		expression::Expression e(x);
		
		expression::Expression e2(expression::NaryType::AND, { e, e });
		expression::Expression e3(expression::NaryType::AND, { e, e, e2 });
		
		e.isITE();
		
		std::cout << e2 << std::endl;
		std::cout << e3 << std::endl;
		
		expression::ExpressionVisitor visitor;
		visitor.setPre(expression::ExpressionVisitor::VisitorFunction(&visiting));
		visitor.visit(e2);
	}
	
} 
