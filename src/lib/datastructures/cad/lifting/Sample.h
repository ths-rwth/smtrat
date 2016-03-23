#pragma once

#include <iostream>

#include "../Common.h"

namespace smtrat {
namespace cad {
	class Sample {
	private:
		RAN mValue;
		bool mIsRoot;
		SampleLiftedWith mLiftedWith;
		SampleRootOf mRootOf;
		
	public:
		explicit Sample(const RAN& value): mValue(value), mIsRoot(false) {
			setIsRoot(false);
		}
		explicit Sample(const RAN& value, std::size_t id): mValue(value), mIsRoot(true) {
			setIsRoot(true);
			mRootOf.set(id);
		}
		const RAN& value() const {
			return mValue;
		}
		bool isRoot() const {
			return mIsRoot;
		}
		void setIsRoot(bool isRoot) {
			mIsRoot = isRoot;
			mValue.setIsRoot(isRoot);
		}
		const SampleLiftedWith& liftedWith() const {
			return mLiftedWith;
		}
		SampleLiftedWith& liftedWith() {
			return mLiftedWith;
		}
		const SampleRootOf& rootOf() const {
			assert(isRoot());
			return mRootOf;
		}
		SampleRootOf& rootOf() {
			assert(isRoot());
			return mRootOf;
		}
		void merge(const Sample& s) {
			if (s.isRoot()) setIsRoot(true);
			mLiftedWith = mLiftedWith | s.mLiftedWith;
			mRootOf = mRootOf | s.mRootOf;
		}
		
		bool operator<(const Sample& s) const {
			return value() < s.value();
		}
		
		friend std::ostream& operator<<(std::ostream& os, const Sample& s) {
			return os << s.mValue << "[" << s.mLiftedWith << "][" << s.mRootOf << "]";
		}
	};
}
}
