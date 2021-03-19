#pragma once

#include "../../Common.h"

#include "ExpressionTypes.h"
#include "ExpressionContent.h"

namespace smtrat {
namespace expression {

	class ExpressionPool: public carl::Singleton<ExpressionPool>
	{
		friend carl::Singleton<ExpressionPool>;
		friend class ExpressionModifier;
	private:
		std::size_t mNextID;
		std::unordered_set<ExpressionContent*> mPool;
		
	protected:
		ExpressionPool():
			carl::Singleton<ExpressionPool>(),
			mNextID(1),
			mPool()
		{}
			
		const ExpressionContent* add(ExpressionContent* _ec);
	
	public:
		
		const ExpressionContent* create(carl::Variable::Arg var);
		const ExpressionContent* create(ITEType _type, Expression&& _if, Expression&& _then, Expression&& _else);
		const ExpressionContent* create(QuantifierType _type, std::vector<carl::Variable>&& _variables, Expression&& _expression);
		const ExpressionContent* create(UnaryType _type, Expression&& _expression);
		const ExpressionContent* create(BinaryType _type, Expression&& _lhs, Expression&& _rhs);
		const ExpressionContent* create(NaryType _type, Expressions&& _expressions);
		const ExpressionContent* create(NaryType _type, const std::initializer_list<Expression>& _expressions);
		
		template<typename... Args>
		static const ExpressionContent* create(Args&&... args) {
			return ExpressionPool::getInstance().create(std::forward<Args>(args)...);
		}
	};

}
}
