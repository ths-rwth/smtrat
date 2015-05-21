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
	template<typename T>
	bool convert(const std::vector<types::TermType>& from, std::vector<T>& to, TheoryError& errors) const {
		conversion::VectorVariantConverter<T> converter;
		return converter(from, to, errors);
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

template<typename T>
struct Instantiator: public boost::static_visitor<bool> {
private:
	carl::Variable var;
	T replacement;
public:
	template<typename Res>
	bool operator()(Res&) {
		return false;
	}
	bool operator()(FormulaT& f) {
		std::map<carl::Variable, T> r;
		r.emplace(var, replacement);
		f = f.substitute(r);
		return true;
	}
	bool instantiate(carl::Variable::Arg v, const T& repl, types::TermType& result) {
		var = v;
		replacement = repl;
		return boost::apply_visitor(*this, result);
	}
};

struct UserFunctionInstantiator: public FunctionInstantiator {
	std::vector<std::pair<carl::Variable, carl::Sort>> arguments;
	carl::Sort sort;
	types::TermType definition;
	UserFunctionInstantiator(const std::vector<std::pair<carl::Variable, carl::Sort>>& arguments, const carl::Sort& sort, const types::TermType& definition):
		arguments(arguments), sort(sort), definition(definition) {}
};

}
}
