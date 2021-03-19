#ifndef SRC_LIB_MODULES_EQMODULE_PMATRIX_HPP_
#define SRC_LIB_MODULES_EQMODULE_PMATRIX_HPP_

#include <cstdlib>
#include <type_traits>
#include <cstddef>
#include <cstdint>
#include <unordered_map>

#include "datastructures/alloc.h"
#include "PairHash.h"

namespace smtrat {
	/**
	 * A map that maps from a pair of std::size_t integers to T.
	 * Initially, the idea for that was a simple matrix; this, however,
	 * turned out to be to expensive memory-wise, thus, a hash-based map
	 * is used instead (this makes use of the sparseness of the entries).
	 */
	template<typename T> class pmatrix {
		public:
			pmatrix() : mData() {}

			/**
			 * Find (or default-construct) the entry at position i,j.
			 */
			T& at(std::size_t i, std::size_t j) {
				return mData[std::make_pair(i,j)];
			}

			/**
			 * Find the entry at position i,j.
			 * Returns null if there is no such entry.
			 */
			T* find(std::size_t i, std::size_t j) {
				auto iter = mData.find(std::make_pair(i,j));

				if(iter == mData.end())
					return nullptr;

				return &(iter->second);
			}

			/**
			 * Erase the entry at position i,j.
			 * In the matrix context, this means re-initialization
			 * of the object at that position using the default constructor.
			 */
			void erase(std::size_t i, std::size_t j) {
				mData.erase(std::make_pair(i, j));
			}

			/**
			 * Important in the matrix context (where it adds another row/column).
			 * For the matrix, this does nothing.
			 */
			void add() {}

		private:
			std::unordered_map<
				std::pair<std::size_t, std::size_t>,
				T,
				pairhash<std::size_t, std::size_t>,
				std::equal_to<std::pair<std::size_t, std::size_t>>
//                    ,
//				fixedsize_allocator<std::pair<std::size_t, std::size_t>>
			> mData;
	};
}

#endif /* SRC_LIB_MODULES_EQMODULE_PMATRIX_HPP_ */
