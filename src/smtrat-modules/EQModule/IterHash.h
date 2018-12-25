#ifndef SRC_LIB_MODULES_EQMODULE_ITERHASH_H_
#define SRC_LIB_MODULES_EQMODULE_ITERHASH_H_
#pragma once

#include <iterator>

namespace smtrat {
	/**
	 * Hash an iterator by the pointed-to address.
	 */
	template<typename IterType> struct by_address_hasher {
		typedef typename std::iterator_traits<IterType>::pointer pointer_type;

		std::size_t operator()(const IterType& iter) const noexcept {
			std::hash<pointer_type> phasher;
			return phasher(&*iter);
		}
	};
}

#endif
