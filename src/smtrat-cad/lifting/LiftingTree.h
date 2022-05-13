#pragma once

#include <carl-common/datastructures/carlTree.h>

#include <smtrat-common/smtrat-common.h>

#include "../common.h"
#include "../utils/CADConstraints.h"

#include "SampleIteratorQueue.h"
#include "SampleComparator.h"

namespace smtrat {
namespace cad {
	template<typename Settings>
	class LiftingTree {
	public:
		using Tree = carl::tree<Sample>;
		using Iterator = Tree::iterator;
		using FSC = FullSampleComparator<Iterator,Settings::fullSampleComparator>;
		using SC = SampleComparator<Iterator,Settings::sampleComparator>;
		using Constraints = CADConstraints<Settings::backtracking>;
	private:
		const Constraints& mConstraints;
		std::vector<carl::Variable> mVariables;
		Tree mTree;
		SampleIteratorQueue<Iterator, FSC> mCheckingQueue;
		SampleIteratorQueue<Iterator, SC> mLiftingQueue;
		std::vector<Iterator> mRemovedFromLiftingQueue;
		
		std::size_t dim() const {
			return mVariables.size();
		}
		
		void addToQueue(Iterator it) {
			assert(it.isValid());
			if (it.depth() < dim()) {
				mLiftingQueue.addNewSample(it);
			} else {
				mCheckingQueue.addNewSample(it);
			}
		}
		
		void cleanQueuesFromExpired() {
			auto removeIf = [&](const auto& it){ return !mTree.is_valid(it); };
			mLiftingQueue.cleanup(removeIf);
			mCheckingQueue.cleanup(removeIf);
			auto it = std::remove_if(mRemovedFromLiftingQueue.begin(), mRemovedFromLiftingQueue.end(), removeIf);
			mRemovedFromLiftingQueue.erase(it, mRemovedFromLiftingQueue.end());
		}
		
		bool insertRootSamples(Iterator parent, std::vector<Sample>& samples) {
			if (samples.empty()) return false;
			std::sort(samples.begin(), samples.end());
			samples.erase(std::unique(samples.begin(), samples.end()), samples.end());
			bool gotNewSamples = false;
			auto tbegin = mTree.begin_children(parent);
			auto tit = tbegin;
			auto tend = mTree.end_children(parent);
			// Insert roots
			for (const auto& s: samples) {
				while (tit != tend && *tit < s) tit++;
				if (tit == tend) {
					// Append as last sample
					auto it = mTree.append(parent, s);
					addToQueue(it);
					gotNewSamples = true;
				} else if (tit->value() == s.value()) {
					// Replace non-root sample
					if (!tit->isRoot()) gotNewSamples = true;
					tit->merge(s);
				} else {
					// Insert before sample
					auto it = mTree.insert(tit, s);
					addToQueue(it);
					gotNewSamples = true;
				}
			}
			return gotNewSamples;
		}
		
		bool mergeRootSamples(Iterator parent, std::vector<Sample>& samples) {
			SMTRAT_LOG_TRACE("smtrat.cad.lifting", "Merging " << samples << " into" << std::endl << mTree);
			bool gotNewSamples = insertRootSamples(parent, samples);
			if (!gotNewSamples) {
				SMTRAT_LOG_TRACE("smtrat.cad.lifting", "Nothing to merge");
				if (mTree.is_leaf(parent)) {
					auto var = mVariables[parent.depth()];
					auto interval = mConstraints.bounds().getInterval(var);
					SMTRAT_LOG_TRACE("smtrat.cad.lifting", "Inserting zero node for " << var << " from " << interval);
					auto it = mTree.append(parent, Sample(RAN(sample(interval))));
					addToQueue(it);
				}
				return false;
			}
			// Add samples
			auto tbegin = mTree.begin_children(parent);
			auto tend = mTree.end_children(parent);
			auto tit = tbegin, tlast = tbegin;
			if (tbegin->isRoot()) {
				auto it = mTree.insert(tbegin, Sample(carl::sample_below(tlast->value())));
				addToQueue(it);
			}
			while (true) {
				tit++;
				if (tit == tend) break;
				if (tlast->isRoot() && tit->isRoot()) {
					auto it = mTree.insert(tit, Sample(carl::sample_between(tlast->value(), tit->value())));
					addToQueue(it);
				}
				tlast = tit;
			}
			if (tlast->isRoot()) {
				auto it = mTree.append(parent, Sample(carl::sample_above(tlast->value())));
				addToQueue(it);
			}
			
			SMTRAT_LOG_TRACE("smtrat.cad.lifting", "Result: " << std::endl << mTree);
			return true;
		}
		
	public:
		LiftingTree(const Constraints& c): mConstraints(c) {}
		LiftingTree(const LiftingTree&) = delete;
		LiftingTree(LiftingTree&&) = delete;
		LiftingTree& operator=(const LiftingTree&) = delete;
		LiftingTree& operator=(LiftingTree&&) = delete;
		
		const auto& getTree() const {
			return mTree;
		}
		const auto& getLiftingQueue() const {
			return mLiftingQueue;
		}
		void reset(std::vector<carl::Variable>&& vars) {
			mVariables = std::move(vars);
			mCheckingQueue.clear();
			mLiftingQueue.clear();
			mRemovedFromLiftingQueue.clear();
			mTree.clear();
			auto it = mTree.setRoot(Sample(RAN(0), false));
			assert(mTree.is_valid(it));
			mLiftingQueue.addNewSample(it);
		}
		
		bool hasFullSamples() const {
			return !mCheckingQueue.empty();
		}
		Iterator getNextFullSample() {
			return mCheckingQueue.removeNextSample();
		}
		void resetFullSamples() {
			SMTRAT_LOG_DEBUG("smtrat.cad.lifting", "Resetting samples of full dimension.");
			mCheckingQueue.clear();
			for (auto it = mTree.begin_depth(dim()); it != mTree.end_depth(); it++) {
				SMTRAT_LOG_DEBUG("smtrat.cad.lifting", "\tadding " << *it);
				mCheckingQueue.addNewSample(it);
			}
		}
		
		bool hasNextSample() const {
			return !mLiftingQueue.empty();
		}
		Iterator getNextSample() {
			assert(mTree.is_valid(mLiftingQueue.getNextSample()));
			return mLiftingQueue.getNextSample();
		}
		void removeNextSample() {
			assert(hasNextSample());
			mRemovedFromLiftingQueue.emplace_back(mLiftingQueue.removeNextSample());
		}
		void restoreRemovedSamples() {
			mLiftingQueue.addNewSamples(mRemovedFromLiftingQueue.begin(), mRemovedFromLiftingQueue.end());
			mRemovedFromLiftingQueue.clear();
		}
		
		bool liftSample(Iterator sample, const UPoly& p, std::size_t pid) {
			assert(isConsistent());
			auto m = extractSampleMap(sample);
			SMTRAT_LOG_DEBUG("smtrat.cad.lifting", "Lifting " << m << " on " << p);
			std::vector<Sample> newSamples;
			// TODO: Check whether the polynomials becomes zero (check if McCallum is safe)
			auto result = carl::real_roots(p, m, RationalInterval::unbounded_interval());
			if (!result.is_univariate() || result.roots().empty()) {
				SMTRAT_LOG_DEBUG("smtrat.cad.lifting", "\tnew root sample: " << RAN(0));
				newSamples.emplace_back(RAN(0), pid);
			} else {
				for (const auto& r: result.roots()) {
					SMTRAT_LOG_DEBUG("smtrat.cad.lifting", "\tnew root sample: " << r);
					newSamples.emplace_back(r, pid);
				}
			}
			auto bounds = mConstraints.bounds().getInterval(mVariables[sample.depth()]);
			if (bounds.lower_bound_type() != carl::BoundType::INFTY) {
				newSamples.emplace_back(RAN(bounds.lower()), true);
			}
			if (bounds.upper_bound_type() != carl::BoundType::INFTY) {
				newSamples.emplace_back(RAN(bounds.upper()), true);
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.lifting", "\tmerging " << newSamples);
			return mergeRootSamples(sample, newSamples);
		}
		bool addTrivialSample(Iterator sample) {
			if (!mTree.is_leaf(sample)) return false;
			SMTRAT_LOG_DEBUG("smtrat.cad.lifting", "Variables: " << mVariables);
			SMTRAT_LOG_DEBUG("smtrat.cad.lifting", "For " << printSample(sample));
			auto variable = mVariables[sample.depth()];
			auto center = carl::sample(mConstraints.bounds().getInterval(variable));
			SMTRAT_LOG_DEBUG("smtrat.cad.lifting", "Selecting " << center << " for " << variable << " from " << mConstraints.bounds().getInterval(variable));
			auto it = mTree.append(sample, Sample(RAN(center), false));
			addToQueue(it);
			
			for (std::size_t i = 1; i < Settings::trivialSampleRadius; i++) {
				auto itpos = mTree.append(sample, Sample(RAN(center + i), false));
				addToQueue(itpos);
				auto itneg = mTree.append(sample, Sample(RAN(center - i), false));
				addToQueue(itneg);
			}
			return true;
		}
		Assignment extractSampleMap(Iterator it) const {
			SMTRAT_LOG_TRACE("smtrat.cad.lifting", "Extracting sample from" << std::endl << mTree);
			SMTRAT_LOG_TRACE("smtrat.cad.lifting", "Variables: " << mVariables);
			Assignment res;
			auto cur = mTree.begin_path(it);
			while (cur != mTree.end_path() && !cur.isRoot()) {
				res.emplace(mVariables[cur.depth()-1], cur->value());
				cur++;
			}
			SMTRAT_LOG_TRACE("smtrat.cad.lifting", "Result: " << res);
			return res;
		}
		
		void removedPolynomialsFromLevel(std::size_t level, const carl::Bitset& mask) {
			SMTRAT_LOG_DEBUG("smtrat.cad.lifting", "Cleanup after removing " << mask << " from level " << level);
			for (auto it = mTree.begin_depth(level - 1); it != mTree.end_depth(); it++) {
				it->liftedWith() -= mask;
			}
			std::vector<Iterator> deleteQueue;
			for (auto it = mTree.begin_depth(level); it != mTree.end_depth(); it++) {
				if (!it->isRoot()) continue;
				it->rootOf() -= mask;
				if (it->rootOf().none()) {
					deleteQueue.emplace_back(it);
					deleteQueue.emplace_back(mTree.left_sibling(Iterator(it)));
				}
			}
			for (const auto& it: deleteQueue) {
				SMTRAT_LOG_TRACE("smtrat.cad.lifting", "Purging " << printSample(it));
				mTree.erase(it);
			}
			cleanQueuesFromExpired();
		}
		
		void removedConstraint(const carl::Bitset& mask) {
			for (auto& s: mTree) {
				if (s.evaluatedWith().size() == 0) continue;
				SMTRAT_LOG_DEBUG("smtrat.cad.lifting", "Purging " << s.evaluatedWith() << " by " << mask);
				s.evaluatedWith() -= mask;
				s.evaluationResult() -= mask;
			}
		}
		
		bool isConsistent() const {
			if (!mCheckingQueue.isConsistent()) return false;
			if (!mLiftingQueue.isConsistent()) return false;
			return true;
		}

		std::string printSample(Iterator sample) const {
			std::vector<Sample> chunks(mTree.begin_path(sample), mTree.end_path());
			std::stringstream ss;
			for (std::size_t d = 0; d < sample.depth(); d++) {
				if (d != 0) ss << " -> ";
				ss << mVariables[d] << " = " << chunks[chunks.size()-2-d];
			}
			return ss.str();
		}
		std::string printFullSamples() const {
			std::stringstream ss;
			for (const auto& it: mCheckingQueue) {
				ss << "\t" << printSample(it) << std::endl;
			}
			return ss.str();
		}
	};
}
}
