#pragma once

#include <type_traits>

#include "Conversions.h"

namespace smtrat {
namespace parser {

struct FunctionInstantiator {
	virtual ~FunctionInstantiator() {}
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
	virtual ~IndexedFunctionInstantiator() {}
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

template<typename V, typename T>
struct Instantiator: public boost::static_visitor<bool> {
protected:
	V var;
	T replacement;
	types::TermType result;
public:
	template<typename Res>
	bool operator()(const Res&) {
		return false;
	}
	bool operator()(carl::Variable v) {
		if (v == var) result = replacement;
		return true;
	}
	template<typename TYPE = T>
	typename std::enable_if<std::is_same<TYPE,Poly>::value, bool>::type
	operator()(const Poly& p) {
		result = carl::substitute(p, var, replacement);
		return true;
	}
	bool operator()(const FormulaT& f) {
		result = carl::substitute(f, var, replacement);
		return true;
	}
	template<typename VAR = V>
	typename std::enable_if<std::is_same<VAR,types::BVVariable>::value, bool>::type
	operator()(const types::BVVariable& v) {
		if (v == var) result = replacement;
		return true;
	}
	template<typename VAR = V>
	typename std::enable_if<std::is_same<VAR,types::BVVariable>::value, bool>::type
	operator()(const types::BVTerm& t) {
		std::map<types::BVVariable,types::BVTerm> m;
		m.emplace(var, replacement);
		result = t.substitute(m);
		return true;
	}
	bool instantiate(V v, const T& repl, types::TermType& subject) {
		var = v;
		replacement = repl;
		if (boost::apply_visitor(*this, subject)) {
			subject = this->result;
			return true;
		}
		return false;
	}
};

struct UserFunctionInstantiator: public FunctionInstantiator {
	std::vector<types::VariableType> arguments;
	carl::Sort sort;
	types::TermType definition;
	std::set<types::VariableType> auxiliaries;
	FormulasT globalFormulas;
	UserFunctionInstantiator(const std::vector<types::VariableType>& arguments, const carl::Sort& sort, const types::TermType& definition, const std::set<types::VariableType>& auxiliaries):
		arguments(arguments), sort(sort), definition(definition), auxiliaries(auxiliaries), globalFormulas() {}
};

}
}
