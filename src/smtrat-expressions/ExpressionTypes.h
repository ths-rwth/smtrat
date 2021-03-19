#pragma once

#include <vector>

namespace smtrat {
namespace expression {
	using carl::operator<<;
	
	class Expression;
	class ExpressionPool;
	
	struct ExpressionContent;
	struct ITEExpression;
	struct QuantifierExpression;
	struct UnaryExpression;
	struct BinaryExpression;
	struct NaryExpression;
	
	std::ostream& operator<<(std::ostream& os, const Expression& expr);
	
	typedef std::vector<Expression> Expressions;
	
	
	enum ITEType { ITE };
	enum QuantifierType { EXISTS, FORALL };
	enum UnaryType { NOT };
	enum BinaryType {  };
	enum NaryType { AND, OR, XOR, IFF };
	
	
	inline std::ostream& operator<<(std::ostream& os, ITEType) {
		return os << "ite";
	}
	inline std::ostream& operator<<(std::ostream& os, QuantifierType type) {
		switch (type) {
			case QuantifierType::EXISTS: return os << "exists";
			case QuantifierType::FORALL: return os << "forall";
		}
	}
	inline std::ostream& operator<<(std::ostream& os, UnaryType type) {
		switch (type) {
			case UnaryType::NOT: return os << "not";
		}
	}
	inline std::ostream& operator<<(std::ostream& os, BinaryType type) {
		switch (type) {
		}
	}
	inline std::ostream& operator<<(std::ostream& os, NaryType type) {
		switch (type) {
			case NaryType::AND: return os << "and";
			case NaryType::OR: return os << "or";
			case NaryType::XOR: return os << "xor";
			case NaryType::IFF: return os << "iff";
		}
	}
}
}

namespace smtrat {
	typedef expression::Expression Expression;
	typedef expression::Expressions Expressions;
}
