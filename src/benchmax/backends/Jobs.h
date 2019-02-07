#pragma once

#include <benchmax/tools/Tools.h>
#include <benchmax/benchmarks/BenchmarkSet.h>

#include <cmath>
#include <numeric>

namespace benchmax {

using Job = std::pair<const Tool*, std::filesystem::path>;

template<typename T>
class RandomizationAdaptor {
public:
	struct iterator: public std::iterator<std::forward_iterator_tag, T, long, const T*, T&> {
	private:
		std::size_t mK = 0;
		std::size_t mFactor;
		const std::vector<T>& mData;
	public:
		iterator(std::size_t k, std::size_t factor, const std::vector<T>& data):
			mK(k), mFactor(factor), mData(data)
		{}
		const T& operator*() {
			return mData[(mK * mFactor) % mData.size()];
		}
		iterator& operator++() {
			++mK;
			return *this;
		}
		bool operator!=(const iterator& rhs) const {
			return mK != rhs.mK;
		}
	};
private:
	const std::vector<T>& mData;
	std::size_t mFactor;
public:
	RandomizationAdaptor(const std::vector<T>& data): mData(data) {
		mFactor = static_cast<std::size_t>(std::sqrt(static_cast<double>(mData.size())));
		while (std::gcd(mData.size(), mFactor) != 1) {
			++mFactor;
		}
	}

	auto begin() const {
		return iterator{ 0, mFactor, mData };
	}
	auto end() const {
		return iterator{ mData.size(), mFactor, mData };
	}
};

class Jobs {
	const Tools& mTools;
	const BenchmarkSet& mFiles;
	std::vector<Job> mJobs;
public:
	Jobs(const Tools& tools, const BenchmarkSet& benchmarks):
		mTools(tools), mFiles(benchmarks) {
		for (const auto& t: tools) {
			for (const auto& b: benchmarks) {
				if (t->canHandle(b)) {
					mJobs.emplace_back(t.get(), b);
				}
			}
		}
	}

	const auto& tools() const {
		return mTools;
	}
	const auto& files() const {
		return mFiles;
	}

	auto size() const {
		return mJobs.size();
	}

	/// Begin iterator.
	auto begin() const {
		return mJobs.begin();
	}
	/// End iterator.
	auto end() const {
		return mJobs.end();
	}
	auto randomized() const {
		return RandomizationAdaptor(mJobs);
	}
};

}