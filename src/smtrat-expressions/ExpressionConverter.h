#pragma once

#include <boost/variant.hpp>

#include "../../Common.h"

#include "ExpressionTypes.h"

namespace smtrat {
namespace expression {
	
	struct ExpressionConverter: boost::static_visitor<FormulaT> {
	protected:
		FormulasT mGlobalFormulas;
		FormulaT convert(const Expression& expr) {
			return boost::apply_visitor(*this, expr.getContent().content);
		}
	public:
		
		FormulaT operator()(carl::Variable::Arg var) {
			return FormulaT(var);
		}
		FormulaT operator()(const ITEExpression& expr) {
			//FormulaT _if = convert(expr.condition);
			//mGlobalFormulas.
			return FormulaT();
		}
		FormulaT operator()(const QuantifierExpression& expr) {
			return FormulaT();
		}
		FormulaT operator()(const UnaryExpression& expr) {
			FormulaT arg = convert(expr.expression);
			switch (expr.type) {
				case NOT:
					return FormulaT(carl::FormulaType::NOT, std::move(arg));
			}
		}
		FormulaT operator()(const BinaryExpression& expr) {
			FormulaT lhs = convert(expr.lhs);
			FormulaT rhs = convert(expr.rhs);
			switch (expr.type) {
			}
		}
		FormulaT operator()(const NaryExpression& expr) {
			FormulasT args;
			for (const auto& e: expr.expressions) {
				args.push_back(convert(e));
			}
			switch (expr.type) {
				case NaryType::AND:
					return FormulaT(carl::FormulaType::AND, std::move(args));
				case NaryType::OR:
					return FormulaT(carl::FormulaType::OR, std::move(args));
				case NaryType::XOR:
					return FormulaT(carl::FormulaType::XOR, std::move(args));
				case NaryType::IFF:
					return FormulaT(carl::FormulaType::IFF, std::move(args));
			}
		}
		
		FormulaT operator()(const Expression& expr) {
			FormulaT res = convert(expr);
			if (mGlobalFormulas.empty()) return res;
			mGlobalFormulas.push_back(res);
			res = FormulaT(carl::FormulaType::AND, std::move(mGlobalFormulas));
			// Safe as argued in http://stackoverflow.com/a/9168917
			mGlobalFormulas.clear();
			return res;
		}
	};
	
}
}
