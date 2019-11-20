#ifndef SMTRAT_EQMODULE_VARIANT_HASH_H_INCLUDED_
#define SMTRAT_EQMODULE_VARIANT_HASH_H_INCLUDED_

#pragma once

#include <boost/variant/static_visitor.hpp>
#include <boost/variant.hpp>
#include <unordered_map>
#include <cstddef>

/**
 * Implements a specialization of std::hash for any boost::variant.
 * This only works if the types of the variant are std::hash-enabled (have a std::hash specialization of their own).
 */

namespace smtrat {
	struct variant_hash_visitor : public boost::static_visitor<std::size_t> {
		template<typename T> std::size_t operator()(const T& value) const noexcept {
			std::hash<T> hasher;
			return hasher(value);
		}
	};
}

#if BOOST_VERSION < 107100
namespace std {
	template<BOOST_VARIANT_ENUM_PARAMS(typename Args)> struct hash< boost::variant<BOOST_VARIANT_ENUM_PARAMS(Args)> > {
		size_t operator()(const boost::variant<BOOST_VARIANT_ENUM_PARAMS(Args)>& var) const noexcept {
			return boost::apply_visitor(smtrat::variant_hash_visitor(), var);
		}
	};

	template<BOOST_VARIANT_ENUM_PARAMS(typename Args)> struct hash< const boost::variant<BOOST_VARIANT_ENUM_PARAMS(Args)> > {
		size_t operator()(const boost::variant<BOOST_VARIANT_ENUM_PARAMS(Args)>& var) const noexcept {
			return boost::apply_visitor(smtrat::variant_hash_visitor(), var);
		}
	};
}
#endif

#endif
