#ifndef SRC_LIB_MODULES_EQMODULE_EQMODULEHASH_TPP_
#define SRC_LIB_MODULES_EQMODULE_EQMODULEHASH_TPP_

#include "EQModule.h"

namespace smtrat {
	template<typename Settings>
		EQModule<Settings>::hash_bucket_set::hash_bucket_set(EQModule& module, UninterpretedFunction fn) :
			mModule(module),
			mArity(fn.domain().size()),
			mBinShift(InitialCapacityShift),
			mBucketCount(0),
			mBinPtr(new bin[1 << InitialCapacityShift]()),
			mBucketAlloc(sizeof(bucket) + sizeof(class_vector_entry)*(mArity-1)),
			mEntryAlloc(sizeof(entry)),
			mTmpClasses(new class_vector_entry[mArity])
	{}

	template<typename Settings>
		EQModule<Settings>::hash_bucket_set::~hash_bucket_set()
	{
		delete[] mTmpClasses;
		delete[] mBinPtr;
	}

	template<typename Settings>
		void EQModule<Settings>::hash_bucket_set::P_merge_buckets(bucket* target, bucket* source)
	{
		target->mEntries.merge(source->mEntries);

		for(implicit_edge_info *ptr : source->supportedEdges) {
			ptr->mSupportingBucket = target;
		}

		target->supportedEdges.consume(std::move(source->supportedEdges));
	}

	template<typename Settings>
		auto EQModule<Settings>::hash_bucket_set::P_find_bucket(bin& b, const class_vector_entry* classes, std::size_t hvalue) -> bucket*
	{
		for(bucket &cur : b) {
			if(cur.hashValue == hvalue) {
				for(std::size_t i = 0; i < mArity; ++i) {
					if(cur.classes[i].mClass != classes[i].mClass) {
						continue;
					}
				}

				return &cur;
			}
		}

		return nullptr;
	}

	template<typename Settings>
		auto EQModule<Settings>::hash_bucket_set::find(g_iterator finstance) -> bucket*
	{
		const g_iterator* args = mModule.argsof(finstance);

		// compute the vector of argument classes
		for(std::size_t i = 0; i < mArity; ++i) {
			mTmpClasses[i].mClass = mModule.mComponentUnionFind.find(mModule.mUnionFind.find(args[i]->second.mUFIndex));
		}

		// compute the hash
		std::size_t hvalue = P_compute_hash(mTmpClasses);
		bin& targetBin = mBinPtr[P_reduce_hash(hvalue)];

		// actually find the bucket
		bucket* result = P_find_bucket(targetBin, mTmpClasses, hvalue);
		assert(result);
		return result;
	}

	template<typename Settings>
		void EQModule<Settings>::hash_bucket_set::P_insert_bucket(bin& bin_, bucket* bucket_)
	{
		bin_.push_front(bucket_);
		++mBucketCount;
	}

	template<typename Settings>
		void EQModule<Settings>::hash_bucket_set::P_remove_bucket(bin& bin_, bucket* bucket_)
	{
		bin_.erase(bucket_);
		--mBucketCount;
	}

	template<typename Settings>
		void EQModule<Settings>::hash_bucket_set::P_remove_from_bucket_list(bucket* bucket_, std::size_t argIndex)
	{
		const std::size_t c = bucket_->classes[argIndex].mClass;
		const std::size_t n = bucket_->classes[argIndex].mBucketListIndex;
		bucket_->classes[argIndex].mBucketListIndex = std::numeric_limits<std::size_t>::max();

		std::vector<bucket_list_entry>& l = mModule.mComponentUnionFind[c].mBuckets;

		assert(n == std::numeric_limits<std::size_t>::max() || (n < l.size() && l[n].mBucket == bucket_));
		if(n < l.size()) {
			bucket_list_entry &rep = l.back();
			assert(rep.mBucket->classes[rep.mFirstIndex].mClass == c);
			rep.mBucket->classes[rep.mFirstIndex].mBucketListIndex = n;
			std::swap(rep, l[n]);
			l.pop_back();
		}
	}

	template<typename Settings>
		void EQModule<Settings>::hash_bucket_set::remove_from_bucket_lists(bucket* bucket_)
	{
		for(std::size_t i = 0; i < mArity; ++i) {
			P_remove_from_bucket_list(bucket_, i);
		}
	}

	template<typename Settings>
		void EQModule<Settings>::hash_bucket_set::P_erase_bucket(bucket* bucket_, std::size_t ignoreClass)
	{
		assert(bucket_->mEntries.empty());

		// remove bucket_ from the list of changed buckets if its still on there
		mChanged.erase_if_present(bucket_);

		// remove from bucket lists (ignore oldClass as its bucket list will be cleared manually)
		for(std::size_t i = 0; i < mArity; ++i) {
			if(bucket_->classes[i].mClass != ignoreClass) {
				P_remove_from_bucket_list(bucket_, i);
			}
		}

		bucket_->~bucket();
		mBucketAlloc.free(bucket_);
	}

	template<typename Settings>
		void EQModule<Settings>::hash_bucket_set::P_detach_bucket(bin& bin_, bucket* bucket_)
	{
		// remove the bucket from its bin
		P_remove_bucket(bin_, bucket_);

		// remove bucket_ from the list of changed buckets
		mChanged.erase_if_present(bucket_);

		// remove bucket_ from the bucket lists
		remove_from_bucket_lists(bucket_);

		// remove bucket from the list of buckets that need updating
		mNeedUpdate.erase_if_present(bucket_);
	}

	template<typename Settings>
		void EQModule<Settings>::hash_bucket_set::P_detach_bucket_from_split(bin& bin_, bucket* bucket_)
	{
		// remove the bucket from its bin
		P_remove_bucket(bin_, bucket_);

		// remove bucket_ from the list of changed buckets
		mChanged.erase_if_present(bucket_);

		// remove bucket_ from the bucket lists of split classes
		for(std::size_t i = 0; i < mArity; ++i) {
			if(mModule.mComponentUnionFind[bucket_->classes[i].mClass].mIsSplit) {
				P_remove_from_bucket_list(bucket_, i);
			}
		}
	}

	template<typename Settings>
		void EQModule<Settings>::hash_bucket_set::P_add_split(bucket*& firstSplit, bucket*& lastSplit, bucket* b)
	{
		if(b->nextSplit == nullptr && b != lastSplit) {
			if(firstSplit == nullptr) {
				lastSplit = b;
			}

			b->nextSplit = firstSplit;
			firstSplit = b;
		}
	}

	template<typename Settings>
		std::size_t EQModule<Settings>::hash_bucket_set::P_insert_into_bucket_list(std::size_t class_, bucket* bucket_, std::size_t firstIndex)
	{
		// bucket lists MUST be unique, assert that
		assert(
			std::find_if(
				mModule.mComponentUnionFind[class_].mBuckets.begin(),
				mModule.mComponentUnionFind[class_].mBuckets.end(),
				[&] (const bucket_list_entry& e) { return (e.mBucket == bucket_); }
			) == mModule.mComponentUnionFind[class_].mBuckets.end()
		);

		std::size_t result = mModule.mComponentUnionFind[class_].mBuckets.size();
		mModule.mComponentUnionFind[class_].mBuckets.emplace_back(this, bucket_, firstIndex);
		return result;
	}

	template<typename Settings>
		void EQModule<Settings>::hash_bucket_set::P_insert_into_bucket_lists(bucket* b)
	{
		const std::size_t thisAge = ++mModule.mLocalSplitAge;

		for(std::size_t arg = 0; arg < mArity; ++arg) {
			const std::size_t c = b->classes[arg].mClass;
			const bool foundprev = (mModule.mComponentUnionFind[c].mLastSeenInSplit == thisAge);

			if(!foundprev) {
				mModule.mComponentUnionFind[c].mLastSeenInSplit = thisAge;
				b->classes[arg].mBucketListIndex = P_insert_into_bucket_list(c, b, arg);
			} else {
				b->classes[arg].mBucketListIndex = std::numeric_limits<std::size_t>::max();
			}
		}
	}

	template<typename Settings>
		auto EQModule<Settings>::hash_bucket_set::insert_function_instance(g_iterator term_iter) -> bucket*
	{
		if(mBucketCount+1 > static_cast<std::size_t>((LoadFactor::num << mBinShift) / LoadFactor::den)) {
			P_resize();
		}

		const g_iterator *args = mModule.argsof(term_iter);
		assert(mArity == mModule.arityof(term_iter));

		bucket* bptr = &(mBucketAlloc.emplace());
		entry *eptr = &(mEntryAlloc.emplace());
		eptr->value = term_iter;

		for(std::size_t i = 0; i < mArity; ++i) {
			bptr->classes[i].mClass = mModule.mComponentUnionFind.find(mModule.mUnionFind.find(args[i]->second.mUFIndex));
		}

		bptr->hashValue = P_compute_hash(bptr->classes);
		bin& targetBin = mBinPtr[P_reduce_hash(bptr->hashValue)];

		bucket* target = P_find_bucket(targetBin, bptr->classes, bptr->hashValue);
		if(target) {
#ifdef SMTRAT_DEVOPTION_Statistics
			if(Settings::collectHashStatistics) {
				mModule.mStatistics->countBucketMerged();
			}
#endif

			bptr->~bucket();
			mBucketAlloc.free(bptr);
			target->mEntries.push_back_nonempty(eptr);
			mChanged.add_front(target);
			return target;
		} else {
#ifdef SMTRAT_DEVOPTION_Statistics
			if(Settings::collectHashStatistics) {
				if(!targetBin.empty()) {
					mModule.mStatistics->countHashCollision(P_reduce_hash(bptr->hashValue));
				}

				mModule.mStatistics->countBucketInsertion();
			}
#endif

			P_insert_bucket(targetBin, bptr);
			bptr->mEntries.assign(eptr);
			eptr->next = eptr->prev = nullptr;
			P_insert_into_bucket_lists(bptr);
			return bptr;
		}
	}

	template<typename Settings>
		auto EQModule<Settings>::hash_bucket_set::P_construct_bucket(const class_vector_entry* classes, std::size_t hashValue, entry* e) -> bucket*
	{
		bucket* bptr = &(mBucketAlloc.emplace());
		bptr->hashValue = hashValue;

		for(std::size_t i = 0; i < mArity; ++i) {
			bptr->classes[i].mClass = classes[i].mClass;
		}

		bptr->mEntries.assign(e);
		e->prev = e->next = nullptr;
		return bptr;
	}

	template<typename Settings>
		auto EQModule<Settings>::hash_bucket_set::P_insert_during_split(bucket*& firstSplit, bucket*& lastSplit, entry* e) -> bucket*
	{
		if(mBucketCount+1 > static_cast<std::size_t>((LoadFactor::num << mBinShift) / LoadFactor::den)) {
			P_resize();
		}

		assert(mArity == mModule.arityof(e->value));

		const g_iterator *args = mModule.argsof(e->value);

		for(std::size_t i = 0; i < mArity; ++i) {
			std::size_t c  = mModule.mUnionFind.find(args[i]->second.mUFIndex);
			mTmpClasses[i].mClass = c;
		}

		const std::size_t hashValue = P_compute_hash(mTmpClasses);
		bin& targetBin = mBinPtr[P_reduce_hash(hashValue)];

		bucket* target = P_find_bucket(targetBin, mTmpClasses, hashValue);
		if(target) {
#ifdef SMTRAT_DEVOPTION_Statistics
			if(Settings::collectHashStatistics) {
				mModule.mStatistics->countBucketMerged();
			}
#endif

			target->mEntries.push_back_nonempty(e);
			mChanged.add_front(target);
			P_add_split(firstSplit, lastSplit, target);
			return target;
		} else {
#ifdef SMTRAT_DEVOPTION_Statistics
			if(Settings::collectHashStatistics) {
				if(!targetBin.empty()) {
					mModule.mStatistics->countHashCollision(P_reduce_hash(hashValue));
				}

				mModule.mStatistics->countBucketInsertion();
			}
#endif

			bucket* bptr = P_construct_bucket(mTmpClasses, hashValue, e);

			P_insert_bucket(targetBin, bptr);
			P_insert_into_bucket_lists(bptr);
			mNeedUpdate.push_front(bptr);
			return bptr;
		}
	}

	template<typename Settings>
		void EQModule<Settings>::hash_bucket_set::P_update_bucket(bucket *b, std::size_t oldClass, std::size_t newClass)
	{
		std::size_t i = 0;
		b->hashValue = 0;

		for(; i < mArity; ++i) {
			const std::size_t c = b->classes[i].mClass;

			if(c == oldClass) {
				P_update_hash_step(b->hashValue, newClass, i);
				goto oldClassFirst; // the use of goto here is for saving a lot of unnecessary comparisons
			} else {
				P_update_hash_step(b->hashValue, c, i);

				if(c == newClass) {
					goto newClassFirst;
				}
			}
		}

		// old class not found
		assert(false);

		// we found the new class first (before finding oldClass);
		// no need to update bucket list indices, no need to add bucket to newClass bucket list
newClassFirst:
		for(++i; i < mArity; ++i) {
			const std::size_t c = b->classes[i].mClass;

			if(c == oldClass) {
				P_update_hash_step(b->hashValue, newClass, i);
				b->classes[i].mBucketListIndex = std::numeric_limits<std::size_t>::max();
				b->classes[i].mClass = newClass;
				goto tail;
			}

			P_update_hash_step(b->hashValue, c, i);
		}

		// old class not found
		assert(false);

		// we found the old class first (before finding newClass);
		// we have to update the bucket list index here and if we
		// do not find new class, add the bucket to its bucket list
oldClassFirst: {
			std::size_t newFirstIndex = i; // remember the new first index of newClass
			b->classes[i].mClass = newClass;

			for(++i; i < mArity; ++i) {
				const std::size_t c = b->classes[i].mClass;

				if(c == oldClass) {
					b->classes[i].mClass = newClass;
					P_update_hash_step(b->hashValue, newClass, i);
				} else if(c == newClass) {
					mModule.mComponentUnionFind[c].mBuckets[b->classes[i].mBucketListIndex].mFirstIndex = newFirstIndex;
					b->classes[newFirstIndex].mBucketListIndex = b->classes[i].mBucketListIndex;
					b->classes[i].mBucketListIndex = std::numeric_limits<std::size_t>::max();
					P_update_hash_step(b->hashValue, newClass, i);
					goto tail;
				} else {
					P_update_hash_step(b->hashValue, c, i);
				}
			}

			b->classes[newFirstIndex].mBucketListIndex = P_insert_into_bucket_list(newClass, b, newFirstIndex);
			return;
		}

tail: // we have seen both newClass and oldClass
		for(++i; i < mArity; ++i) {
			const std::size_t c = b->classes[i].mClass;

			if(c == oldClass) {
				b->classes[i].mClass = newClass;
				P_update_hash_step(b->hashValue, newClass, i);
			} else {
				P_update_hash_step(b->hashValue, c, i);
			}
		}
	}

	template<typename Settings>
		void EQModule<Settings>::hash_bucket_set::P_update_hash_step(std::size_t& hvalue, std::size_t c, std::size_t)
	{
		hash_combine(hvalue, c);
	}

	template<typename Settings>
		std::size_t EQModule<Settings>::hash_bucket_set::P_reduce_hash(std::size_t hvalue) const
	{
		return hvalue & ((1 << mBinShift) - 1);
	}

	template<typename Settings>
		std::size_t EQModule<Settings>::hash_bucket_set::P_compute_hash(const class_vector_entry* classes) const
	{
		std::size_t hvalue = 0;

		for(std::size_t i = 0; i < mArity; ++i) {
			hash_combine(hvalue, classes[i].mClass);
		}

		return hvalue;
	}

	template<typename Settings>
		void EQModule<Settings>::hash_bucket_set::P_redistribute_buckets(bin* newBins)
	{
		const std::size_t mBins = 1 << mBinShift;

		for(std::size_t i = 0; i < mBins; ++i) {
			bin& currentBin = mBinPtr[i];

			if(!currentBin.empty()) {
				bin &beven = newBins[i];
				bin &bodd = newBins[i + mBins];

				bucket *cur;
				while((cur = currentBin.pop_front()) != nullptr) {
					if(cur->hashValue & mBins) {
						bodd.push_back(cur);
					} else {
						beven.push_back(cur);
					}
				}
			}
		}
	}

	template<typename Settings>
		auto EQModule<Settings>::hash_bucket_set::merge_class_into(bucket* b, std::size_t oldClass, std::size_t newClass) -> bucket*
	{
		assert(!b->mEntries.empty());
		assert(oldClass != newClass);

		bin& sourceBin = mBinPtr[P_reduce_hash(b->hashValue)];
		P_update_bucket(b, oldClass, newClass);
		P_remove_bucket(sourceBin, b);

		bin& targetBin = mBinPtr[P_reduce_hash(b->hashValue)];
		bucket* target = P_find_bucket(targetBin, b->classes, b->hashValue);

		if(target) {
#ifdef SMTRAT_DEVOPTION_Statistics
			if(Settings::collectHashStatistics) {
				mModule.mStatistics->countBucketMerged();
			}
#endif

			P_merge_buckets(target, b);
			mChanged.add_front(target);
			P_erase_bucket(b, oldClass);
			return target;
		} else {
#ifdef SMTRAT_DEVOPTION_Statistics
			if(Settings::collectHashStatistics) {
				if(!targetBin.empty()) {
					mModule.mStatistics->countHashCollision(P_reduce_hash(b->hashValue));
				}

				mModule.mStatistics->countBucketInsertion();
			}
#endif

			P_insert_bucket(targetBin, b);
			return b;
		}
	}

	template<typename Settings>
		void EQModule<Settings>::hash_bucket_set::split_bucket(bucket* b)
	{
		if(b->mEntries.trivial()) { // trivial bucket. simply update it and keep it.
			// detach bucket from all data structures (bucket lists of split classes, its bin, changed list)
			// note that not detaching it from the non-split classes REQUIRES that no class may be merged into
			// a class that did not split during this split operation
			P_detach_bucket_from_split(mBinPtr[P_reduce_hash(b->hashValue)], b);

			const std::size_t thisAge = ++mModule.mLocalSplitAge;
			b->hashValue = 0;

			for(std::size_t i = 0; i < mArity; ++i) {
				const std::size_t c = b->classes[i].mClass;

				if(mModule.mComponentUnionFind[c].mIsSplit) {
					const std::size_t newClass = mModule.mUnionFind.find(mModule.argsof(b->mEntries.front()->value)[i]->second.mUFIndex);

					b->classes[i].mClass = newClass;
					P_update_hash_step(b->hashValue, newClass, i);

					if(mModule.mComponentUnionFind[newClass].mLastSeenInSplit != thisAge) {
						// first occurrence of newClass in this split operation
						mModule.mComponentUnionFind[newClass].mLastSeenInSplit = thisAge;
						std::vector<bucket_list_entry> &list = mModule.mComponentUnionFind[newClass].mBuckets;
						b->classes[i].mBucketListIndex = list.size();
						list.emplace_back(this, b, i);
					} else {
						// not the first occurrence of newClass in this split operation
						b->classes[i].mBucketListIndex = std::numeric_limits<std::size_t>::max();
					}
				} else {
					// the class can not change in this case
					P_update_hash_step(b->hashValue, c, i);
				}
			}

			bin& targetBin = mBinPtr[P_reduce_hash(b->hashValue)];

			assert(!P_find_bucket(targetBin, b->classes, b->hashValue));
			P_insert_bucket(targetBin, b);

			mNeedUpdate.add_front(b);

			b->splitAge = mModule.mGlobalSplitAge;
		} else { // here we will always end up deleting the old bucket
			P_detach_bucket(mBinPtr[P_reduce_hash(b->hashValue)], b);

			bucket* firstSplit = nullptr, *lastSplit = nullptr;
			for(auto cur = b->mEntries.begin(); cur != b->mEntries.end(); ) {
				entry &tmp = *cur; ++cur;
				bucket* result = P_insert_during_split(firstSplit, lastSplit, &tmp);
				result->splitAge = mModule.mGlobalSplitAge;
			}

			for(bucket* cur = firstSplit; cur != nullptr; ) {
				assert(!cur->mEntries.trivial() && cur->supportedEdges.empty());

				const std::size_t thisAge = ++mModule.mLocalSplitAge;

				for(entry &ecur : cur->mEntries) {
					mModule.mComponentUnionFind[ecur.value->second.mUFIndex].mLastSeenInSplit = thisAge;
				}

				for(std::size_t i = 0; i < b->supportedEdges.size(); ) {
					implicit_edge_info *edge = b->supportedEdges[i];

					if(
						mModule.mComponentUnionFind[edge->mRealPred->second.mUFIndex].mLastSeenInSplit == thisAge &&
						mModule.mComponentUnionFind[edge->mRealSucc->second.mUFIndex].mLastSeenInSplit == thisAge
					) {
						cur->supportedEdges.emplace_back(edge);
						std::swap(b->supportedEdges.back(), b->supportedEdges[i]);
						b->supportedEdges.pop_back();
						edge->mSupportingBucket = cur;
					} else {
						++i;
					}
				}

				bucket* tmp = cur;
				cur = cur->nextSplit;
				tmp->nextSplit = nullptr;
			}

			for(implicit_edge_info *edge : b->supportedEdges) {
				g_iterator pred = edge->mPred;
				g_iterator succ = edge->mSucc;

				assert(pred == edge->mOther->mSucc);
				assert(succ == edge->mOther->mPred);
				assert(edge->mSupportingBucket == b && edge->mOther->mSupportingBucket == nullptr);

				mModule.mDeletedEdges.emplace_back(pred, succ);
				mModule.mDeletedEdges.emplace_back(succ, pred);

				succ->second.mImplicit.remove_destroy(edge->mOther);
				pred->second.mImplicit.remove_destroy(edge);
			}

			b->~bucket();
			mBucketAlloc.free(b);
		}
	}

	template<typename Settings>
		void EQModule<Settings>::hash_bucket_set::P_resize()
	{
#ifdef SMTRAT_DEVOPTION_Statistics
		if(Settings::collectHashStatistics) {
			mModule.mStatistics->countRehashed();
		}
#endif

		std::size_t newBinSize = 1 << (mBinShift+1);
		bin *newBins = new bin[newBinSize]();
		P_redistribute_buckets(newBins);
		delete[] mBinPtr;
		mBinPtr = newBins;
		++mBinShift;
	}

	template<typename Settings>
		void EQModule<Settings>::process_merge_lists()
	{
		bool change;

		do {
			change = false;
			
			// iterate over all uninterpreted functions
			for(typename function_map_type::iterator i = mFunctionMap.begin(), fend = mFunctionMap.end(); i != fend; ++i) {
				hash_buckets_type& buckets = i->second.mHashBuckets;
				hash_bucket_type* cur;

				// iterate over the corresponding change list
				while((cur = buckets.mChanged.pop_front()) != nullptr) {
					// all buckets in the change list must contain more than one function instance entry
					assert(!cur->mEntries.trivial());

					// find the component-level representative of the first entry
					hash_bucket_entry* first = cur->mEntries.front();
					std::size_t cfirst = mUnionFind.find(first->value->second.mUFIndex);
					std::size_t ccfirst = mComponentUnionFind.find(cfirst);

					// union that with all other entries in the bucket
					for(hash_bucket_entry* e = first->next; e != nullptr; e = e->next) {
						g_iterator value = e->value;
						std::size_t csecond = mUnionFind.find(e->value->second.mUFIndex);
						std::size_t ccsecond = mComponentUnionFind.find(csecond);

						// if the entries are not equivalent on the component level already
						if(ccfirst != ccsecond) {
							bool curDeleted = false;
							change = true;

							std::size_t newClass = mComponentUnionFind.fast_union(ccfirst, ccsecond);
							std::size_t oldClass = ((ccfirst == newClass) ? ccsecond : ccfirst);
							
							// remove ineq edges between these components, moving them to mPossibleInconsistencies
							P_cc_union_for_ineq(oldClass, newClass);

							// add the additional implicit edge
							implicit_edge_info* supported = P_add_implicit_edge(mUnionFind[cfirst], mUnionFind[csecond], first->value, value);

							// check for and add (if applicable) an implicit edge deduction
							P_add_implicit_edge_deduction(supported->mRealPred, supported->mRealSucc);

							// set the supporting bucket
							supported->mSupportingBucket = cur;
							cur->supportedEdges.emplace_back(supported);

							// the vector of buckets containing oldClass
							std::vector<bucket_list_entry>& sourceVector = mComponentUnionFind[oldClass].mBuckets;

							// iterate the buckets updated by this merge
							for(const auto& update_bucket : sourceVector) {
								// merge the classes in the bucket
								hash_bucket_type *target = update_bucket.mBucketSet->merge_class_into(update_bucket.mBucket, oldClass, newClass);

								if(update_bucket.mBucket == cur && target != cur) {
									// we merged the bucket cur into another bucket.
									// as this bucket is in the worklist after the merge,
									// stop the loop AFTER finishing the update of all affected buckets
									assert(!curDeleted);
									curDeleted = true;
								}
							}

							// clear the sourceVector (all buckets that contained oldClass as argument no longer do);
							// to not disturb the iteration above, they are not removed in merge_class_into
							sourceVector.clear();

							// update the component class of the first entry
							ccfirst = newClass;

							// handle the current-bucket-deleted case by restarting iteration over change list
							if(curDeleted) break;
						}
					}
				}
			}
		} while(change);
	}

	template<typename Settings>
		void EQModule<Settings>::P_merge_buckets(std::size_t oldClass, std::size_t newClass)
	{
		std::vector<bucket_list_entry>& buckets = mComponentUnionFind[oldClass].mBuckets;

		// iterate over the list of buckets containing oldClass
		for(bucket_list_entry& entry : buckets) {
			hash_bucket_type* target = entry.mBucketSet->merge_class_into(entry.mBucket, oldClass, newClass);

			// check invariant: either the bucket was deleted, or it is now part of the bucket list for newClass
			assert(
				target != entry.mBucket ||
				std::find_if(
					mComponentUnionFind[newClass].mBuckets.begin(),
					mComponentUnionFind[newClass].mBuckets.end(),
					[&] (const bucket_list_entry& e) -> bool { return e.mBucket == entry.mBucket; }
				)  != mComponentUnionFind[newClass].mBuckets.end()
			); (void)target;
		}

		// clear the sourceVector (all buckets that contained oldClass as argument no longer do);
		// to not disturb the iteration above, they are not removed in merge_class_into
		buckets.clear();
	}

	template<typename Settings>
		void EQModule<Settings>::hash_bucket_set::P_post_split_update_classes()
	{
		bucket* cur;

		// run through the list of buckets that might need an update until it is empty
		while((cur = mNeedUpdate.pop_front()) != nullptr) {
			bool changed = false;

			// check whether we need to change anything
			std::size_t i, oldClass, newClass;
			for(i = 0; i < mArity; ++i) {
				oldClass = cur->classes[i].mClass; assert(mModule.mUnionFind.find(oldClass) == oldClass);
				newClass = mModule.mComponentUnionFind.find(oldClass);

				if(oldClass != newClass) {
					changed = true; break;
				}
			}

			if(changed) {
				// remove the bucket from all datastructures
				P_remove_bucket(mBinPtr[P_reduce_hash(cur->hashValue)], cur);
				remove_from_bucket_lists(cur);

				// update the classes
				cur->classes[i].mClass = newClass;
				for(++i; i < mArity; ++i) {
					oldClass = cur->classes[i].mClass; assert(mModule.mUnionFind.find(oldClass) == oldClass);
					cur->classes[i].mClass = mModule.mComponentUnionFind.find(oldClass);
				}

				// recompute the hash
				cur->hashValue = P_compute_hash(cur->classes);
				bin &targetBin = mBinPtr[P_reduce_hash(cur->hashValue)];

				// search re-insertion point
				bucket* target = P_find_bucket(targetBin, cur->classes, cur->hashValue);

				if(target) {
					// equivalent bucket existed
					P_merge_buckets(target, cur);
					mChanged.add_front(target);
					mChanged.erase_if_present(cur);
					cur->~bucket();
					mBucketAlloc.free(cur);
				} else {
					// equivalent bucket did not exist
#ifdef SMTRAT_DEVOPTION_Statistics
					if(Settings::collectHashStatistics) {
						if(!targetBin.empty()) {
							mModule.mStatistics->countHashCollision(P_reduce_hash(cur->hashValue));
						}

						mModule.mStatistics->countBucketInsertion();
					}
#endif

					// reinsert bucket into its bucket lists
					P_insert_into_bucket_lists(cur);
					// reinsert bucket into its bin
					P_insert_bucket(targetBin, cur);
				}
			}
		}
	}

	template<typename Settings>
		void EQModule<Settings>::P_post_split_update_classes()
	{
		// iterate the change list (only once), removing all entries, updating all classes according to union find.
		// reinsert all nontrivial buckets for further (merge) processing
		// this is necessary as we can not use mComponentUnionFind during a split operation before all split operations are completed
		for(auto&& entry : mFunctionMap) {
			entry.second.mHashBuckets.P_post_split_update_classes();
		}
	}

	template<typename Settings>
		void EQModule<Settings>::P_split_buckets()
	{
		// this age value is used to determine whether some bucket still needs processing
		++mGlobalSplitAge;

		// iterate over the split classes and split buckets corresponding to them
		for(std::size_t split : mSplitClasses) {
			// its important to iterate with integral index and from the end here;
			// the split method most likely removes/adds/swaps some elements during this iteration
			std::vector<bucket_list_entry>& list = mComponentUnionFind[split].mBuckets;

			for(std::size_t i = list.size() - 1; i < list.size(); --i) {
				bucket_list_entry& b = list[i];

				// if this bucket has not been processed, split it now
				if(b.mBucket->splitAge != mGlobalSplitAge) {
					b.mBucketSet->split_bucket(b.mBucket); // note, b may be invalid after this call!
				}
			}
		}

		// reset the split flag
		for(std::size_t split : mSplitClasses) {
			mComponentUnionFind[split].mIsSplit = false;
		}

		mSplitClasses.clear();
	}
}

#endif /* SRC_LIB_MODULES_EQMODULE_EQMODULEHASH_TPP_ */
