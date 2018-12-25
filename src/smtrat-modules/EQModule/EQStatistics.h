/**
 * @file EQStatistics.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2014-10-19
 * Created on 2014-10-19.
 */


#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <lib/utilities/stats/Statistics.h>
#include <boost/lexical_cast.hpp>
#include <iterator>

namespace smtrat
{
	template<typename Settings>
		class EQStatistics : public Statistics
	{
	private:
		// Members.
		std::size_t mHashCollisions, mBucketInsertions, mBucketMerges, mRehashes;
		std::unordered_map< std::size_t, std::size_t > mHashCounts;

		std::size_t mConstructedInfeasibleSubsets;

		std::size_t mCheckedUnassignedLiterals;
		std::size_t mDeducedUnassignedLiterals;

		std::size_t mAddedImplicitDeductions;

		static constexpr std::size_t reportMostFrequentValues = 128;

	public:
		// Override Statistics::collect.
		void collect()
		{
			if(Settings::collectHashStatistics) {
				Statistics::addKeyValuePair("hash_collisions", mHashCollisions);
				Statistics::addKeyValuePair("bucket_insertions", mBucketInsertions);
				Statistics::addKeyValuePair("bucket_merges", mBucketMerges);
				Statistics::addKeyValuePair("rehashes", mRehashes);

				std::vector<std::pair<std::size_t, std::size_t>> entries;

				std::copy(mHashCounts.begin(), mHashCounts.end(), std::back_inserter(entries));
				std::sort(entries.begin(), entries.end(),
					[&] (const std::pair<std::size_t, std::size_t> first, const std::pair<std::size_t, std::size_t>& second) {
						return first.second > second.second;
					}
				);

				std::size_t cnt = 0;
				for(const std::pair<std::size_t, std::size_t>& e : entries) {
					Statistics::addKeyValuePair("most_frequent_hash_value_"+boost::lexical_cast<std::string>(cnt+1), boost::lexical_cast<std::string>(e.first) + " occurred " + boost::lexical_cast<std::string>(e.second) + " times");
					if(++cnt == reportMostFrequentValues) break;
				}
			}

			Statistics::addKeyValuePair("constructed_infeasible_subsets", mConstructedInfeasibleSubsets);
			
			if(Settings::deduceUnassignedLiterals) {
				Statistics::addKeyValuePair("checked_unassigned_literals", mCheckedUnassignedLiterals);
				Statistics::addKeyValuePair("deduced_unassigned_literals", mDeducedUnassignedLiterals);
			}
			
			if(Settings::addImplicitEdgeDeductions) {
				Statistics::addKeyValuePair("implicit_edge_deductions", mAddedImplicitDeductions);
			}
		}

		void countHashCollision(std::size_t reducedHashValue) noexcept {
			typename decltype(mHashCounts)::iterator iter;
			bool inserted;

			std::tie(iter, inserted) = mHashCounts.emplace(reducedHashValue, std::size_t(1));
			if(!inserted) {
				++(iter->second);
			}

			++mHashCollisions;
		}

		void countBucketInsertion() noexcept { ++mBucketInsertions; }
		void countBucketMerged() noexcept { ++mBucketMerges; }
		void countRehashed() noexcept { ++mRehashes; }

		void countInfeasibleSubsets() noexcept { ++mConstructedInfeasibleSubsets; }

		void countCheckedUnassignedLiterals() noexcept { ++mCheckedUnassignedLiterals; }
		void countDeducedUnassignedLiterals() noexcept { ++mDeducedUnassignedLiterals; }

		void countImplicitEdgeDeduction() noexcept { ++mAddedImplicitDeductions; }

		explicit EQStatistics(const std::string& _statisticName = "EQStatistics") :
			Statistics( _statisticName, this ),
			mHashCollisions(0),
			mBucketInsertions(0),
			mBucketMerges(0),
			mRehashes(0),
			mConstructedInfeasibleSubsets(0),
			mCheckedUnassignedLiterals(0),
			mDeducedUnassignedLiterals(0),
			mAddedImplicitDeductions(0)
		{}

		~EQStatistics() {}
	};
}

#endif
