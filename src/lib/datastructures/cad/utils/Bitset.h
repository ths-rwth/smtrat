#pragma once

#include <iostream>

#include <boost/dynamic_bitset.hpp>

namespace smtrat {
namespace cad {
	
	/**
	 * This class is a simple wrapper around boost::dynamic_bitset.
	 * Its purpose is to allow for on-the-fly resizing of the bitset.
	 * Formally, a Bitset object represents an infinite bitset that starts with the bits stored in mData extended by mDefault.
	 * Whenever a bit is written that is not yet stored explicitly in mData or two Bitset objects with different mData sizes are involved, the size of mData is expanded transparently.
	 */
	class Bitset {
	public:
		using BaseType = boost::dynamic_bitset<>;
		static auto constexpr npos = BaseType::npos;
		static auto constexpr bits_per_block = BaseType::bits_per_block;
	private:
		mutable BaseType mData;
		bool mDefault;
		void ensureSize(std::size_t pos) {
			if (pos >= mData.size()) {
				mData.resize(pos+1);
			}
		}
	public:
		Bitset(bool defaultValue = false): mDefault(defaultValue) {}
		Bitset(BaseType&& base, bool defaultValue): mData(std::move(base)), mDefault(defaultValue) {}
		Bitset(const std::initializer_list<std::size_t>& bits, bool defaultValue = false): mDefault(defaultValue) {
			for (auto b: bits) set(b);
		}
		
		auto resize(std::size_t num_blocks) const -> decltype(mData.resize(num_blocks, mDefault)) {
			return mData.resize(num_blocks, mDefault);
		}
		
		Bitset& operator-=(const Bitset& rhs) {
			assert(mDefault == rhs.mDefault);
			alignSize(*this, rhs);
			mData -= rhs.mData;
			return *this;
		}
		Bitset& operator|=(const Bitset& rhs) {
			assert(mDefault == rhs.mDefault);
			alignSize(*this, rhs);
			mData |= rhs.mData;
			return *this;
		}
		
		Bitset& set(std::size_t n, bool value = true) {
			ensureSize(n);
			mData.set(n, value);
			return *this;
		}
		Bitset& reset(std::size_t n) {
			ensureSize(n);
			mData.reset(n);
			return *this;
		}
		bool test(std::size_t n) const {
			if (n >= mData.size()) return mDefault;
			return mData.test(n);
		}
		bool any() const {
			assert(!mDefault);
			return mData.any();
		}
		bool none() const {
			assert(!mDefault);
			return mData.none();
		}
		
		auto count() const noexcept {
			return mData.count();
		}
		
		auto size() const {
			return mData.size();
		}
		auto num_blocks() const {
			return mData.num_blocks();
		}
		auto find_first() const {
			return mData.find_first();
		}
		auto find_next(std::size_t pos) const {
			return mData.find_next(pos);
		}
		
		friend void alignSize(const Bitset& lhs, const Bitset& rhs) {
			if (lhs.size() < rhs.size()) lhs.resize(rhs.size());
			else if (lhs.size() > rhs.size()) rhs.resize(lhs.size());
		}
		
		friend bool operator==(const Bitset& lhs, const Bitset& rhs) {
			assert(lhs.mDefault == rhs.mDefault);
			alignSize(lhs, rhs);
			return lhs.mData == rhs.mData;
		}
		friend bool operator<(const Bitset& lhs, const Bitset& rhs) {
			if (lhs.size() < rhs.size()) return true;
			if (lhs.size() > rhs.size()) return false;
			return lhs.mData < rhs.mData;
		}
		
		friend Bitset operator&(const Bitset& lhs, const Bitset& rhs) {
			assert(lhs.mDefault == rhs.mDefault);
			alignSize(lhs, rhs);
			return Bitset(lhs.mData & rhs.mData, lhs.mDefault);
		}
		friend Bitset operator|(const Bitset& lhs, const Bitset& rhs) {
			assert(lhs.mDefault == rhs.mDefault);
			alignSize(lhs, rhs);
			return Bitset(lhs.mData | rhs.mData, lhs.mDefault);
		}
		
		friend std::ostream& operator<<(std::ostream& os, const Bitset& b) {
			return os << b.mData << "@" << b.mDefault;
		}
	};
}
}
