#pragma once

#include "Conversions.h"

namespace smtrat {
namespace parser {

struct FunctionInstantiator {
	template<typename T>
	bool convert(const std::vector<types::TermType>& from, std::vector<T>& to) const {
		conversion::VectorVariantConverter<T> converter;
		return converter(from, to);
	}
	virtual bool operator()(const std::vector<types::TermType>&, types::TermType&, TheoryError& errors) const {
		errors.next() << "Instantiation of this function is not supported.";
		return false;
	}
};
struct IndexedFunctionInstantiator {
	template<typename T>
	bool convert(const std::vector<types::TermType>& from, std::vector<T>& to) const {
		conversion::VectorVariantConverter<T> converter;
		return converter(from, to);
	}
	virtual bool operator()(const std::vector<std::size_t>&, const std::vector<types::TermType>&, types::TermType&, TheoryError& errors) const {
		errors.next() << "Instantiation of this function is not supported.";
		return false;
	}
};
struct UserFunctionInstantiator: public FunctionInstantiator {
private:
	std::vector<std::pair<std::string, carl::Sort>> arguments;
	carl::Sort sort;
	types::TermType definition;
public:
	UserFunctionInstantiator(const std::vector<std::pair<std::string, carl::Sort>>& arguments, const carl::Sort& sort, const types::TermType& definition):
		arguments(arguments), sort(sort), definition(definition) {}
};

}
}
