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
		
	public:
		Sample(const RAN& value, bool isRoot = true): mValue(value), mIsRoot(isRoot) {}
		const RAN& value() const {
			return mValue;
		}
		bool isRoot() const {
			return mIsRoot;
		}
		void setIsRoot(bool isRoot) {
			mIsRoot = isRoot;
		}
		const SampleLiftedWith& liftedWith() const {
			return mLiftedWith;
		}
		SampleLiftedWith& liftedWith() {
			return mLiftedWith;
		}
		
		bool operator<(const Sample& s) const {
			return value() < s.value();
		}
		
		friend std::ostream& operator<<(std::ostream& os, const Sample& s) {
			return os << s.mValue << "[" << s.mLiftedWith << "]";
		}
	};
}
}
