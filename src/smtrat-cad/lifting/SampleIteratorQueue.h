#pragma once

#include "../common.h"
#include "../utils/DynamicPriorityQueue.h"

#include <algorithm>

namespace smtrat {
namespace cad {
	template<typename Iterator, typename Comparator>
	class SampleIteratorQueue {
	private:
		PriorityQueue<Iterator, Comparator> mQueue;
	public:
		auto begin() const {
			return mQueue.begin();
		}
		auto end() const {
			return mQueue.end();
		}
		template<typename InputIt>
		void assign(InputIt begin, InputIt end) {
			mQueue.assign(begin, end);
		}
		void clear() {
			mQueue.clear();
		}
		template<typename Filter>
		void cleanup(Filter&& f) {
			auto it = std::remove_if(mQueue.begin(), mQueue.end(), f);
			mQueue.erase(it, mQueue.end());
		}
		bool empty() const {
			return mQueue.empty();
		}
		Iterator getNextSample() {
			return mQueue.top();
		}
		void addNewSample(Iterator it) {
			mQueue.push(it);
		}
		template<typename InputIt>
		void addNewSamples(InputIt begin, InputIt end) {
			for (auto it = begin; it != end; it++) {
				mQueue.push(*it);
			}
		}
		Iterator removeNextSample() {
			auto it = mQueue.top();
			mQueue.pop();
			return it;
		}
		
		bool isConsistent() const {
			for (const auto& it: mQueue) {
				if (!it.isValid()) return false;
			}
			return true;
		}
		
	};
	template<typename I, typename C>
	inline std::ostream& operator<<(std::ostream& os, const SampleIteratorQueue<I,C>& siq) {
		for (const auto& it: siq) {
			os << *it << "@" << it.depth() << ", ";
		}
		return os;
	}
}
}
