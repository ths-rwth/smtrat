#pragma once

#include <vector>
#include <boost/functional/hash.hpp>

#include "ExpressionContent.h"

namespace std {
	
	template<typename T>
	struct hash<std::vector<T>> {
		std::size_t operator()(const std::vector<T>& v) const {
			std::size_t seed = 0;
			std::hash<T> h;
			for (const auto& t: v) boost::hash_combine(seed, h(t));
			return seed;
		}
	};
	
	template<typename... Args>
	struct hash<boost::variant<Args...>>: boost::static_visitor<std::size_t> {
		template<typename T>
		std::size_t operator()(const T& t) const {
			return std::hash<T>()(t);
		}
		std::size_t operator()(const boost::variant<Args...>& content) const {
			return boost::apply_visitor(*this, content);
		}
	};
	
	struct hash_combiner {
		std::size_t seed;
		hash_combiner(std::size_t _seed = 0): seed(_seed) {}
		hash_combiner& operator()(std::size_t h) {
			boost::hash_combine(seed, h);
			return *this;
		}
		template<typename T>
		hash_combiner& operator()(const T& t) {
			boost::hash_combine(seed, std::hash<T>()(t));
			return *this;
		}
		operator std::size_t() const {
			return seed;
		}
	};
		
	template<>
	struct hash<smtrat::expression::Expression> {
		std::size_t operator()(const smtrat::expression::Expression& expr) const {
			return expr.mContent->hash;
		}
	};
	
	template<>
	struct hash<smtrat::expression::ITEExpression> {
		std::size_t operator()(const smtrat::expression::ITEExpression& ec) const {
			std::hash_combiner hc;
			hc(ec.condition)(ec.thencase)(ec.elsecase);
			return hc;
		}
	};
	template<>
	struct hash<smtrat::expression::QuantifierExpression> {
		std::size_t operator()(const smtrat::expression::QuantifierExpression& ec) const {
			std::hash_combiner hc(std::size_t(ec.type));
			hc(ec.variables)(ec.expression);
			return hc;
		}
	};
	template<>
	struct hash<smtrat::expression::UnaryExpression> {
		std::size_t operator()(const smtrat::expression::UnaryExpression& ec) const {
			std::hash_combiner hc(std::size_t(ec.type));
			hc(ec.expression);
			return hc;
		}
	};
	template<>
	struct hash<smtrat::expression::BinaryExpression> {
		std::size_t operator()(const smtrat::expression::BinaryExpression& ec) const {
			std::hash_combiner hc(std::size_t(ec.type));
			hc(ec.lhs)(ec.rhs);
			return hc;
		}
	};
	template<>
	struct hash<smtrat::expression::NaryExpression> {
		std::size_t operator()(const smtrat::expression::NaryExpression& ec) const {
			std::hash_combiner hc(std::size_t(ec.type));
			hc(ec.expressions);
			return hc;
		}
	};
	template<>
	struct hash<const smtrat::expression::ExpressionContent*> {
		std::size_t operator()(const smtrat::expression::ExpressionContent* ec) const {
			return ec->hash;
		}
	};
}
