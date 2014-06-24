/**
 * @file VariantMap.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <cxxabi.h>
#include <boost/variant.hpp>

namespace smtrat {

template <class T> struct is_variant : std::false_type {};
template <class... U> struct is_variant<boost::variant<U...>> : std::true_type {};
template <class... U> struct is_variant<const boost::variant<U...>> : std::true_type {};

template<typename Key, typename Value>
class VariantMap : public std::map<Key, Value> {
	static_assert(is_variant<Value>::value, "VariantMap is designed for Values of type boost::variant only.");
private:
	std::string demangle(const char* t) const {
		int status;
		char* res = abi::__cxa_demangle(t, 0, 0, &status);
		std::string type(res);
		std::free(res);
		return type;
	}
public:
	template<typename T, typename Output>
	void assertType(const Key& key, Output out) const {
		auto it = this->find(key);
		if (it == this->end()) {
			out() << "No value was set for " << key << ".";
		} else if (boost::get<T>(&(it->second)) == nullptr) {
			out() << "The type of " << key << " should be \"" << demangle(typeid(T).name()) << "\" but is \"" << demangle(it->second.type().name()) << "\".";
		}
	}
	
	template<typename T>
	bool has(const Key& key) const {
		auto it = this->find(key);
		if (it == this->end()) return false;
		return boost::get<T>(&(it->second)) != nullptr;
	}
	template<typename T>
	const T& get(const Key& key) const {
		auto it = this->find(key);
		return boost::get<T>(it->second);
	}
};

}