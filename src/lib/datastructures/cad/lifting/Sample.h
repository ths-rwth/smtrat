#pragma once

#include "../Common.h"

#include <iostream>
#include <limits>

namespace smtrat {
namespace cad {
	class Sample {
	private:
		std::size_t mID = std::numeric_limits<std::size_t>::max();
		RAN mValue;
		bool mIsRoot;
		SampleLiftedWith mLiftedWith;
		SampleRootOf mRootOf;
		Bitset mEvaluatedWith;
		Bitset mEvaluationResult;
		
	public:
		explicit Sample(const RAN& value): mValue(value), mIsRoot(false) {
			setIsRoot(false);
		}
		explicit Sample(const RAN& value, bool isRoot): mValue(value), mIsRoot(isRoot) {
			setIsRoot(isRoot);
		}
		explicit Sample(const RAN& value, std::size_t id): mValue(value), mIsRoot(true) {
			setIsRoot(true);
			mRootOf.set(id);
		}
		const RAN& value() const {
			return mValue;
		}
		const auto& id() const {
			return mID;
		}
		auto& id() {
			return mID;
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
		const Bitset& evaluatedWith() const {
			return mEvaluatedWith;
		}
		Bitset& evaluatedWith() {
			return mEvaluatedWith;
		}
		const Bitset& evaluationResult() const {
			return mEvaluationResult;
		}
		Bitset& evaluationResult() {
			return mEvaluationResult;
		}
		bool hasConflictWithConstraint() const {
			return mEvaluationResult.any();
		}
		void merge(const Sample& s) {
			if (s.isRoot()) setIsRoot(true);
			mLiftedWith = mLiftedWith | s.mLiftedWith;
			mRootOf = mRootOf | s.mRootOf;
		}
		
		bool operator<(const Sample& s) const {
			return value() < s.value();
		}
		bool operator>(const Sample& s) const {
			return s.value() < value();
		}
		
		friend std::ostream& operator<<(std::ostream& os, const Sample& s) {
			return os << s.mValue << "[" << s.mLiftedWith << "][" << s.mRootOf << "]";
		}
	};
}
}
