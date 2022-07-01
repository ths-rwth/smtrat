#pragma once

#include <smtrat-common/smtrat-common.h>

#include <boost/variant.hpp>

#include <iostream>
#include <sstream>

namespace smtrat {
namespace parser {

	struct TheoryError {
	private:
		std::stringstream ss;
		std::string currentTheory;
	public:
		TheoryError& operator()(const std::string& theory) {
			currentTheory = theory;
			return *this;
		}
		friend inline std::ostream& operator<<(std::ostream& os, const TheoryError& te) {
			return os << te.ss.str();
		}
		TheoryError& next() {
			ss << std::endl << "\t" << currentTheory << ": ";
			return *this;
		}
		template<typename T>
		TheoryError& operator<<(const T& t) {
			ss << t;
			return *this;
		}
	};

	struct Identifier {
		std::string symbol;
		std::vector<std::size_t>* indices;
		Identifier(): symbol(""), indices(nullptr) {}
		Identifier(const std::string& symbol): symbol(symbol), indices(nullptr) {}
		Identifier(const std::string& symbol, const std::vector<std::size_t>& indices): symbol(symbol), indices(new std::vector<std::size_t>(indices)) {}
		Identifier(const std::string& symbol, const std::vector<Integer>& indices): symbol(symbol), indices(new std::vector<std::size_t>(indices.size())) {
			for (std::size_t i = 0; i < indices.size(); i++) {
				(*this->indices)[i] = carl::to_int<carl::uint>(indices[i]);
			}
		}
		Identifier& operator=(const Identifier& i) {
			symbol = i.symbol;
			delete indices;
			indices = nullptr;
			if (i.indices != nullptr) indices = new std::vector<std::size_t>(*i.indices);
			return *this;
		}
		Identifier(const Identifier& i) {
			symbol = i.symbol;
			indices = nullptr;
			if (i.indices != nullptr) indices = new std::vector<std::size_t>(*i.indices);
		}
		~Identifier() {
			delete indices;
		}
		operator std::string() const {
			if (indices == nullptr || indices->size() == 0) {
				return symbol;
			}
			std::stringstream ss;
			ss << symbol << "|" << indices->front();
			for (std::size_t i = 1; i < indices->size(); i++) ss << "," << (*indices)[i];
			return ss.str();
		}
	};
	inline std::ostream& operator<<(std::ostream& os, const Identifier& identifier) {
		return os << std::string(identifier);
	}
	
	template<typename T>
	struct SExpressionSequence;
	template<typename T>
	using SExpression = boost::variant<T, boost::recursive_wrapper<SExpressionSequence<T>>>;
	template<typename T>
	struct SExpressionSequence: public std::vector<SExpression<T>> {
		SExpressionSequence(const std::vector<SExpression<T>>& v): std::vector<SExpression<T>>(v) {}
		SExpressionSequence(std::vector<SExpression<T>>&& v): std::vector<SExpression<T>>(std::move(v)) {}
	};
	template<typename T>
	inline std::ostream& operator<<(std::ostream& os, const SExpressionSequence<T>& ses) {
		return os << std::vector<SExpression<T>>(ses);
	}

}
}
