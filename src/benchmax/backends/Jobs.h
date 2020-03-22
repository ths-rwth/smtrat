#pragma once

#include <benchmax/tools/Tools.h>
#include <benchmax/benchmarks/BenchmarkSet.h>

#include <cmath>
#include <numeric>

namespace benchmax {

/// Typedef for a job, consisting of a tool and an input file.
using Job = std::pair<const Tool*, std::filesystem::path>;

/**
 * Provides iteration over a given std::vector in a pseudo-randomized order.
 * Internally, it computes a factor that is coprime to the number of jobs (and thus generates all indices).
 * We choose the factor in the order of the square root of the number of jobs.
 */
template<typename T>
class RandomizationAdaptor {
public:
	struct iterator: public std::iterator<std::forward_iterator_tag, T, long, const T*, T&> {
	private:
		std::size_t mK = 0;
		std::size_t mFactor;
		const std::vector<T>& mData;
	public:
		/// Create a randomized iterator.
		iterator(std::size_t k, std::size_t factor, const std::vector<T>& data):
			mK(k), mFactor(factor), mData(data)
		{}
		/// Dereference iterator.
		const T& operator*() {
			return mData[(mK * mFactor) % mData.size()];
		}
		/// Increment iterator.
		iterator& operator++() {
			++mK;
			return *this;
		}
		/// Compare two iterators.
		bool operator!=(const iterator& rhs) const {
			return mK != rhs.mK;
		}
	};
private:
	const std::vector<T>& mData;
	std::size_t mFactor;
public:
	/// Construct a randomized view on the given vector.
	RandomizationAdaptor(const std::vector<T>& data): mData(data) {
		mFactor = static_cast<std::size_t>(std::sqrt(static_cast<double>(mData.size())));
		while (std::gcd(mData.size(), mFactor) != 1) {
			++mFactor;
		}
	}
	/// Return begin of the randomized range.
	auto begin() const {
		return iterator{ 0, mFactor, mData };
	}
	/// Return end of the randomized range.
	auto end() const {
		return iterator{ mData.size(), mFactor, mData };
	}
};

/**
 * Represents a set of jobs, constructed as the cartesian product of a set of tools and a set of benchmarks.
 */
class Jobs {
	const Tools& mTools;
	const BenchmarkSet& mFiles;
	std::vector<Job> mJobs;
public:
	/// Construct jobs from a set of tools and a set of benchmark files.
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

	/// Returns the set of tools.
	const auto& tools() const {
		return mTools;
	}
	/// Returns the set of files.
	const auto& files() const {
		return mFiles;
	}
	/// Returns the overall number of jobs.
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
	/// Returns all jobs in a pseudo-randomized order.
	auto randomized() const {
		return RandomizationAdaptor(mJobs);
	}
};

}