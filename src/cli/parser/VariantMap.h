/**
 * @file VariantMap.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <smtrat-common/smtrat-common.h>

#ifdef __VS
#pragma warning(push, 0)
#include <boost/variant.hpp>
#pragma warning(pop)
#else
#include <boost/variant.hpp>
#include <cxxabi.h>
#endif

#include <map>
#include <string>
#include <cstdlib>

namespace smtrat {

/**
 * States whether a given type is a `boost::variant`.
 * By default, a type is not.
 */
template <class T> struct is_variant : std::false_type {};
/**
 * States that `boost::variant` is indeed a `boost::variant`.
 */
template <BOOST_VARIANT_ENUM_PARAMS(typename U)> struct is_variant<boost::variant<BOOST_VARIANT_ENUM_PARAMS(U)>> : std::true_type {};
/**
 * States that `const boost::variant` is indeed a `boost::variant`.
 */
template <BOOST_VARIANT_ENUM_PARAMS(typename U)> struct is_variant<const boost::variant<BOOST_VARIANT_ENUM_PARAMS(U)>> : std::true_type {};

/**
 * This class is a specialization of `std::map` where the keys are of arbitrary type and the values are of type `boost::variant`.
 *
 * There is no point in using this class if the values are no variants.
 * Most probably, it would not compile anyway and fail to do so with a large bunch of compiler errors.
 * To prevent this, we assert that the value type is indeed a `boost::variant`.
 *
 * Additionally to the standard methods inherited from `std::map`, it implements three additional methods:
 * - `assertType<T>(key, out)`: Asserts that there is a value for the given key and that it has the type `T`. If this is not the case, an appropriate error is written to `out`.
 * - `has<T>(key)`: Checks if there is a value for the given key and if this value has the type `T`.
 * - `get<T>(key)`: Returns the value for the given key as type `T`.
 *
 * @tparam Key Type of keys.
 * @tparam Value Type of values.
 */
template<typename Key, typename Value>
class VariantMap : public std::map<Key, Value> {
	/// Asserts that the value type is a variant.
	static_assert(is_variant<Value>::value, "VariantMap is designed for Values of type boost::variant only.");
private:
	/**
	 * Converts a type string from `typeid` to a human-readable representation.
	 * This function makes use of `abi::__cxa_demangle`.
     * @param t A type string obtained from `typeid`.
     * @return Demangled type string.
     */
	std::string demangle(const char* t) const {
#ifdef __VS
        //TODO find windows specific solution
        std::string type(t);
#else
		int status;
		char* res = abi::__cxa_demangle(t, 0, 0, &status);
		std::string type(res);
		std::free(res);
#endif
		return type;
	}
public:
	/**
	 * Asserts that the value that is associated with the given key has a specified type.
	 *
	 * The assertion holds, if
	 * - there is a value in the map for the given key and
	 * - the stored value has the type `T`.
	 * @tparam T Type that the value should have.
	 * @tparam Output Type of out.
     * @param key Key.
     * @param out Functor returning an output stream.
     */
	template<typename T, typename Output>
	void assertType(const Key& key, Output out) const {
		auto it = this->find(key);
		if (it == this->end()) {
			out() << "No value was set for " << key << ".";
			assert(it != this->end());
		} else if (boost::get<T>(&(it->second)) == nullptr) {
			out() << "The type of " << key << " should be '" << demangle(typeid(T).name()) << "' but is '" << demangle(it->second.type().name()) << "'.";
			assert(boost::get<T>(&(it->second)) != nullptr);
		}
	}

	/**
	 * Checks if there is a value of the specified type for the given key.
	 * @tparam T Type that the value should have.
     * @param key Key.
     * @return If there is a value of this type.
     */
	template<typename T>
	bool has(const Key& key) const {
		auto it = this->find(key);
		if (it == this->end()) return false;
		return boost::get<T>(&(it->second)) != nullptr;
	}
	/**
	 * Returns the value associated with the given key as type `T`.
	 * @tparam T Type of the value.
     * @param key Key.
     * @return Value of key as type `T`.
     */
	template<typename T>
	const T& get(const Key& key) const {
		auto it = this->find(key);
		return boost::get<T>(it->second);
	}
};

}
