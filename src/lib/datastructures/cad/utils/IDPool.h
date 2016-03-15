#pragma once

#include <iostream>

#include "Bitset.h"

namespace smtrat {
namespace cad {
	class IDPool {
	private:
		Bitset mFreeIDs = Bitset(true);
	public:
		std::size_t get() {
			std::size_t pos = mFreeIDs.find_first();
			if (pos == Bitset::npos) {
				pos = mFreeIDs.size();
				mFreeIDs.resize((mFreeIDs.num_blocks() + 1) * Bitset::bits_per_block);
			}
			mFreeIDs.reset(pos);
			return pos;
		}
		void free(std::size_t id) {
			assert(id < mFreeIDs.size());
			mFreeIDs.set(id);
		}
		void purgeUnusedIDs(Bitset& b) const {
			b -= mFreeIDs;
		}
		friend std::ostream& operator<<(std::ostream& os, const IDPool& p) {
			return os << "Free: " << p.mFreeIDs;
		}
	};
}
}
