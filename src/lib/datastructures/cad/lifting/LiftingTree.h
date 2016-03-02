#pragma once

#include <carl/util/carlTree.h>

#include "../Common.h"

#include "LiftingOperator.h"
#include "SampleIteratorQueue.h"
#include "SampleSelector.h"
#include "SampleComparator.h"

namespace smtrat {
namespace cad {
	template<typename Settings>
	class LiftingTree {
		using Tree = carl::tree<Sample>;
		using Iterator = Tree::iterator;
	private:
		Variables mVariables;
		Tree mTree;
		SampleIteratorQueue<Iterator, FullSampleComparator> mCheckingQueue;
		SampleIteratorQueue<Iterator, SampleComparator> mLiftingQueue;
		LiftingOperator<Iterator, Settings> mLifting;
		SampleSelector<Settings> mSelector;
		
		std::size_t dim() const {
			return mVariables.size();
		}
		
		void addToQueue(Iterator it) {
			if (it.depth() < dim()) {
				mLiftingQueue.addNewSample(it);
			} else {
				mCheckingQueue.addNewSample(it);
			}
		}
		
		bool insertRootSamples(Iterator parent, std::vector<Sample>& samples) {
			std::sort(samples.begin(), samples.end());
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
					if (!tit->isRoot()) {
						*tit = s;
						gotNewSamples = true;
					}
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
			SMTRAT_LOG_TRACE("smtrat.cad", "Merging " << samples << " into" << std::endl << mTree);
			bool gotNewSamples = insertRootSamples(parent, samples);
			if (!gotNewSamples) {
				SMTRAT_LOG_TRACE("smtrat.cad", "Nothing to merge");
				return false;
			}
			// Add samples
			auto tbegin = mTree.begin_children(parent);
			auto tend = mTree.end_children(parent);
			auto tit = tbegin, tlast = tbegin;
			if (tbegin->isRoot()) {
				auto it = mTree.insert(tbegin, Sample(mSelector.below(tlast->value()), false));
				addToQueue(it);
			}
			while (true) {
				tit++;
				if (tit == tend) break;
				if (tlast->isRoot() && tit->isRoot()) {
					auto it = mTree.insert(tit, Sample(mSelector.between(tlast->value(), tit->value()), false));
					addToQueue(it);
				}
				tlast = tit;
			}
			if (tlast->isRoot()) {
				auto it = mTree.append(parent, Sample(mSelector.above(tlast->value()), false));
				addToQueue(it);
			}
			
			SMTRAT_LOG_TRACE("smtrat.cad", "Result: " << std::endl << mTree);
			return true;
		}
		
	public:
		LiftingTree(Variables&& vars): mVariables(vars) {
			auto it = mTree.setRoot(Sample(RAN(0)));
			mLiftingQueue.addNewSample(it);
		}
		
		bool hasFullSamples() const {
			return !mCheckingQueue.empty();
		}
		Iterator getNextFullSample() {
			return mCheckingQueue.removeNextSample();
		}
		
		Iterator getNextSample() {
			mLiftingQueue.restoreOrder();
			return mLiftingQueue.getNextSample();
		}
		Iterator removeNextSample() {
			return mLiftingQueue.removeNextSample();
		}
		
		bool liftSample(Iterator sample, const UPoly& p) {
			auto m = extractSampleMap(sample);
			RationalInterval bounds;
			SMTRAT_LOG_TRACE("smtrat.cad", "Lifting " << m << " on " << p);
			std::vector<Sample> newSamples;
			for (const auto& r: carl::rootfinder::realRoots(p, m, bounds, Settings::rootSplittingStrategy)) {
				newSamples.emplace_back(r);
			}
			return mergeRootSamples(sample, newSamples);
		}
		std::map<carl::Variable, RAN> extractSampleMap(Iterator it) const {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Extracting sample from" << std::endl << mTree);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Variables: " << mVariables);
			std::map<carl::Variable, RAN> res;
			auto cur = mTree.begin_path(it);
			while (cur != mTree.end_path() && !cur.isRoot()) {
				res.emplace(mVariables[cur.depth()-1], it->value());
				cur++;
			}
			SMTRAT_LOG_DEBUG("smtrat.cad", "Result: " << res);
			return res;
		}
	};
}
}
