#pragma once

#include "../Common.h"

namespace smtrat {
namespace cad {
	template<typename Iterator, template<typename> class Comparator>
	class SampleIteratorQueue {
	private:
		static constexpr std::size_t mChunkSize = 1024;
		std::vector<Iterator> mQueue;
		std::size_t mChunkCounter = 0;
		Comparator<Iterator> mComparator;
	public:
		auto begin() const -> decltype(mQueue.begin()) {
			return mQueue.begin();
		}
		auto end() const -> decltype(mQueue.end()) {
			return mQueue.end();
		}
		template<typename InputIt>
		void assign(InputIt begin, InputIt end) {
			mQueue.assign(begin, end);
			restoreOrder(true);
		}
		bool empty() const {
			return mQueue.empty();
		}
		Iterator getNextSample() {
			return mQueue.back();
		}
		void addNewSample(Iterator it) {
			mQueue.push_back(it);
			mChunkCounter++;
		}
		template<typename InputIt>
		void addNewSamples(InputIt begin, InputIt end) {
			std::size_t oldSize = mQueue.size();
			mQueue.insert(mQueue.end(), begin, end);
			mChunkCounter += mQueue.size() - oldSize;
		}
		Iterator removeNextSample() {
			auto it = mQueue.back();
			mQueue.pop_back();
			return it;
		}
		void restoreOrder(bool full = false) {
			if (!full && mChunkCounter < mChunkSize && mQueue.size() > mChunkSize) {
				auto chunkStart = mQueue.begin() + (typename std::vector<Iterator>::difference_type)(mQueue.size() - mChunkSize);
				std::sort(chunkStart, mQueue.end(), mComparator);
			} else {
				mChunkCounter = 0;
				std::sort(mQueue.end(), mQueue.end(), mComparator);
			}
		}
	};
}
}
