#ifndef SRC_LIB_MODULES_EQMODULE_PAIRHASH_H_
#define SRC_LIB_MODULES_EQMODULE_PAIRHASH_H_

#include <unordered_map>

namespace smtrat {
	namespace {
		// implements a continuation of the idea of boost::hash_combine to more than 32 bit std::size_t.
		// the magic number is 2^(8*sizeof(std::size_t)) / golden ratio
		constexpr const size_t SIZE_T_GOLDEN_RATIO = static_cast<std::size_t>(
			(static_cast<long double>(std::numeric_limits<std::size_t>::max()) + 1.0l) / 1.618033988749894848204586834365638117720309179805762862135448l
		);
	}

	// it is imho fairly remarkably stupid that the C++11 does not include hash value combination and hashes of pairs
	// do you want xor? this is how you get xor...
	// the idea below is from boost::hash_combine
	static inline void hash_combine(std::size_t& seed, std::size_t hash_value) noexcept {
		seed ^= hash_value + SIZE_T_GOLDEN_RATIO + (seed<<6) + (seed>>2);
	}

	/**
	 * Note that this may NOT be a specialization of std::hash for std::pair,
	 * this is not allowed by the standard as it does not involve a user-defined type.
	 */
	template< typename F, typename S, typename FirstHasher = std::hash<F>, typename SecondHasher = std::hash<S> > struct pairhash {
		std::size_t operator()(const std::pair<F,S>& p) const noexcept {
			FirstHasher fhasher;
			SecondHasher shasher;

			// ideally, this should be some random, runtime-constant value. but we do not need that for DoS-attack prevention
			std::size_t seed = 0;

			hash_combine(seed, fhasher(p.first));
			hash_combine(seed, shasher(p.second));

			return seed;
		}
	};
}

#endif /* SRC_LIB_MODULES_EQMODULE_PAIRHASH_H_ */
