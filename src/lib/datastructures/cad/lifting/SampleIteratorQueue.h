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
		Iterator removeNextSample() {
			auto it = mQueue.back();
			mQueue.pop_back();
			return it;
		}
		void restoreOrder() {
			if (mChunkCounter < mChunkSize && mQueue.size() > mChunkSize) {
				auto chunkStart = mQueue.begin() + (mQueue.size() - mChunkSize);
				std::sort(chunkStart, mQueue.end(), mComparator);
			} else {
				mChunkCounter = 0;
				std::sort(mQueue.end(), mQueue.end(), mComparator);
			}
		}
	};
}
}
