#pragma once

#include <smtrat-common/smtrat-common.h>

#include <algorithm>
#include <list>
#include <map>
#include <vector>

namespace smtrat {
namespace mcsat {
namespace arithmetic {

	
class RootIndexer {
public:
	using RAN = carl::RealAlgebraicNumber<Rational>;
private:
	std::vector<RAN> mRoots;
	std::map<RAN, std::size_t> mMap;
	std::vector<RAN> mSamples;
public:	
	void add(const std::vector<RAN>& list) {
		mRoots.insert(mRoots.end(), list.begin(), list.end());
	}
	void process() {
		std::sort(mRoots.begin(), mRoots.end());
		mRoots.erase(std::unique(mRoots.begin(), mRoots.end()), mRoots.end());
		SMTRAT_LOG_DEBUG("smtrat.nlsat.rootindexer", "Roots: " << mRoots);
		for (std::size_t i = 0; i < mRoots.size(); i++) {
			mMap.emplace(mRoots[i], i);
		}
		mSamples.reserve(2 * mRoots.size() + 1);
		for (std::size_t n = 0; n < mRoots.size(); n++) {
			if (n == 0) mSamples.emplace_back(carl::sampleBelow(mRoots.front()));
			else mSamples.emplace_back(carl::sampleBetween(mRoots[n-1], mRoots[n]));
			mSamples.emplace_back(mRoots[n]);
		}
		if (mRoots.empty()) mSamples.emplace_back(RAN(0));
		else mSamples.emplace_back(carl::sampleAbove(mRoots.back()));
		SMTRAT_LOG_DEBUG("smtrat.nlsat.rootindexer", "Samples: " << mSamples);
	}
	std::size_t size() const {
		return mRoots.size();
	}
	std::size_t operator[](const RAN& ran) const {
		auto it = mMap.find(ran);
		assert(it != mMap.end());
		return it->second;
	}
	const RAN& operator[](std::size_t n) const {
		assert(n < mRoots.size());
		return mRoots[n];
	}
	const RAN& sampleFrom(std::size_t n) const {
		return mSamples[n];
	}
};
inline std::ostream& operator<<(std::ostream& os, const RootIndexer& ri) {
	os << "Roots:" << std::endl;
	for (std::size_t i = 0; i < ri.size(); i++) {
		os << "\t" << i << ": " << ri[i] << std::endl;
	}
	os << "Samples:" << std::endl;
	for (std::size_t i = 0; i < ri.size()*2+1; i++) {
		os << "\t" << i << ": " << ri.sampleFrom(i) << std::endl;;
	}
	return os;
}


}
}
}
